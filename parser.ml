open Prelude
open Monad
open Term

module Dict = Map.Make(String)
module Set  = Set.Make(String)

type associativity = Left | Right | Binder
type kind          = Term | Prop

type sexp =
  | Atom of string
  | Node of sexp list

type command =
  | Eval        of sexp
  | Infer       of sexp
  | Macroexpand of sexp
  | Axiom       of string * sexp
  | Theorem     of string * sexp * sexp
  | Macro       of sexp * sexp
  | Def         of kind * sexp * sexp
  | Constant    of string * sexp list * sexp
  | Constants   of string list * sexp
  | Infix       of associativity * int * string list
  | Variables   of string list
  | Import      of string list
  | Comment     of string
  | Eof

let rec replace x e = function
  | Atom y  -> if x = y then e else Atom y
  | Node ys -> Node (List.map (replace x e) ys)

let rec showSExp = function
  | Node xs -> "(" ^ showSExps xs ^ ")"
  | Atom s  -> s
and showSExps xs = String.concat " " (List.map showSExp xs)

let extend = function
  | Node xs -> xs
  | x       -> [x]

let atom s  = Atom s
let node xs = Node xs

let splitWhile p =
  let rec go ls = function
    | x :: xs when p x -> go (x :: ls) xs
    | xs               -> List.rev ls, xs
  in go []

exception InvalidSyntax of sexp
exception ExpectedIdent of sexp
exception ExpectedNode  of sexp

let expandIdent = function
  | Atom x -> Ident.ident x
  | e      -> raise (ExpectedIdent e)

let expandNode = function
  | Node es -> es
  | e       -> raise (ExpectedNode e)

(* first stage parser *)
let numSubscript =
  ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"]
  |> List.mapi (fun idx s -> token s >> pure idx)
  |> List.fold_left (<|>) failure

let digits ns = let deg = ref 1 in let m = ref 0 in
  List.iter (fun d -> m := !m + d * !deg; deg := !deg * 10) (List.rev ns); !m

let universe = digits <$> (ch 'U' >> many numSubscript)

let ws             = str (fun c -> c = ' ' || c = '\n' || c = '\t' || c = '\t') >> Monad.eps
let keywords       = [":="; "definition"; "predicate"; "macro"; "theorem"; "lemma";
                      "proposition"; "infixl"; "infixr"; "postulate"; "axiom"; "NB";
                      "variables"; "constant"; "constants"; "#macroexpand"; "#infer"; "#eval"]
let reserved       = ['('; ')'; '['; ']'; '\n'; '\t'; '\r'; ' '; ',']
let isReserved   c = List.mem c reserved
let isntReserved c = not (List.mem c reserved)
let isntKeyword  s = not (List.mem s keywords)

let ident = decorateErrors ["ident"] (guard isntKeyword (str isntReserved))
let sexp = fix (fun p ->
  let paren = node <$> (ch '(' >> optional ws >> many p << ch ')') in
  let atom  = atom <$> ident in
  let comma = ch ',' >> pure (Atom ",") in
  let bra   = fix (fun q ->
    let el = (node <$> many ((atom <|> paren <|> q) << optional ws))
    in ch '[' >> optional ws >> sepBy (ch ',' >> optional ws) el << ch ']' >>=
      fun es -> pure (Node (Atom "LIST" :: es))) in
  (atom <|> comma <|> paren <|> bra) << optional ws)

let sexpToplevel = sexp >>= fun x -> many sexp >>= fun xs ->
  pure (match xs with [] -> x | _ -> Node (x :: xs))

let macrodef tok = token tok >> ws >> sexpToplevel >>=
  fun e1 -> optional ws >> token ":=" >> ws >> sexpToplevel >>=
    fun e2 -> pure (e1, e2)

let def   = macrodef "definition" >>= fun (e1, e2) -> pure (Def (Term, e1, e2))
let pred  = macrodef "predicate"  >>= fun (e1, e2) -> pure (Def (Prop, e1, e2))
let macro = macrodef "macro"      >>= fun (e1, e2) -> pure (Macro (e1, e2))

let thm = (token "theorem" <|> token "lemma" <|> token "proposition") >> ws >> ident >>=
  fun i -> ws >> token ":" >> ws >> sexpToplevel >>=
    fun e1 -> token ":=" >> ws >> sexpToplevel >>=
      fun e2 -> pure (Theorem (i, e1, e2))

let axm = (token "axiom" <|> token "postulate") >> ws >> ident >>= fun i ->
  ws >> token ":" >> ws >> sexpToplevel >>= fun e ->
    pure (Axiom (i, e))

let infix assoc tok = token tok >> ws >> ident << ws >>= fun e ->
  sepBy1 ws ident >>= fun is -> pure (Infix (assoc, int_of_string e, is))

let infixl = infix Left  "infixl"
let infixr = infix Right "infixr"

let debug ident fn = token ident >> ws >> sexpToplevel >>= fun e -> pure (fn e)

let comment = token "NB" >> ws >> str (fun c -> c <> '\n' && c <> '\r') >>= fun s -> optional ws >> pure (Comment s)

let constant = token "constant" >> ws >> ident << ws >>=
  fun i -> sexpToplevel >>= fun e0 ->
    let (e, e1) = splitWhile ((<>) (Atom ":")) (expandNode e0)
      in pure (Constant (i, e, Node (List.tl e1)))

let constants = token "constants" >> ws >> sepBy1 ws (guard ((<>) ":") ident) << ws >>=
  fun is -> token ":" >> ws >> sexpToplevel >>= fun e -> pure (Constants (is, e))

let macroexpand = debug "#macroexpand" (fun e -> Macroexpand e)
let infer       = debug "#infer"       (fun e -> Infer e)
let eval        = debug "#eval"        (fun e -> Eval e)

let variables = token "variables" >> ws >> sepBy1 ws ident >>= fun is -> pure (Variables is)
let import = token "import" >> ws >> sepBy1 ws ident >>= fun fs -> pure (Import fs)

let cmdeof = eof >> pure Eof

let cmdline = comment  <|> def       <|> macro  <|> pred      <|> thm
          <|> constant <|> constants <|> axm    <|> infer     <|> eval
          <|> import   <|> infixr    <|> infixl <|> variables <|> macroexpand
          <|> cmdeof

let cmd = optional ws >> cmdline

(* second stage parser *)
let builtinInfix = [
  ",", (1, Binder); "=", (50, Left); "∧", (20, Right); "∨", (30, Right);
  "⊃", (40, Right); "⇒", (40, Right); "∘", (60, Right)
]
let operators = ref (Dict.of_seq (List.to_seq builtinInfix))

(* From: https://rosettacode.org/wiki/Parsing/Shunting-yard_algorithm#OCaml *)
let operator op =
  match Dict.find_opt op !operators with
  | Some e -> e
  | None   -> (-1, Left)

let prec = function
  | Atom op -> fst (operator op)
  | _       -> -1

let rec shuntingyard tokens =
  let unbuf = function
    | []  -> Node []
    | [x] -> x
    | xs  -> Node (List.rev xs)
  in let rec pusher stack buf queue = function
    | [] -> List.rev (unbuf buf :: queue) @ stack
    | Atom op :: xs when Dict.mem op !operators ->
      let mv, stack' = splitWhile (fun op' ->
        match operator op with
        | i, Left   -> i <= prec op'
        | i, Right  -> i <  prec op'
        | i, Binder -> i >  prec op') stack
      in pusher (Atom op :: stack') [] (List.rev mv @ unbuf buf :: queue) xs
    | x :: xs ->
      pusher stack (unpack x :: buf) queue xs
  in let rec poper stack = function
    | [] -> stack
    | Atom op :: xs when Dict.mem op !operators ->
      begin match stack with
        | x :: y :: stack' -> poper (Node [y; Atom op; x] :: stack') xs
        | _ -> failwith "shuntingyard"
      end
    | x :: xs -> poper (x :: stack) xs
  in match (pusher [] [] [] tokens) with
  | []  -> Node []
  | [x] -> x
  | xs  -> unbuf (poper [] xs)

and unpack = function
  | Atom x  -> Atom x
  | Node xs -> shuntingyard xs

let rec ofNat n = if n <= 0 then Zero else Succ (ofNat (n - 1))

let expandVar x =
  match runParser universe (ofString x) 0 with
  | Ok (_, n) -> U (ofNat n)
  | Error _   -> Var (Ident.ident x)

let rec expandTerm = function
  | Atom x                                     -> expandVar x
  | Node [Atom "cod"; x]                       -> Cod (expandTerm x)
  | Node [Atom "dom"; x]                       -> Dom (expandTerm x)
  | Node [Atom "id"; x]                        -> Id  (expandTerm x)
  | Node [f; Atom "∘"; g]                      -> Com (expandTerm f, expandTerm g)
  | Node [Atom "Hom"; t; a; b]                 -> Hom (expandTerm t, expandTerm a, expandTerm b)
  | Node [Atom x; Node (Atom "LIST" :: xs)]    -> Const (Ident.ident x, List.map expandTerm xs)
  | Node (f :: xs)                             -> List.fold_left Term.app (expandTerm f) (List.map expandTerm xs)
  | e                                          -> raise (InvalidSyntax e)

let rec expandProp = function
  | Atom "⊤"                                   -> True
  | Atom "⊥"                                   -> False
  | Node (Atom "¬" :: es)                      -> neg  (expandProp (Node es))
  | Node [a; Atom "∧"; b]                      -> And  (expandProp a, expandProp b)
  | Node [a; Atom "∨"; b]                      -> Or   (expandProp a, expandProp b)
  | Node [a; Atom "⊃"; b]                      -> Impl (expandProp a, expandProp b)
  | Node [a; Atom "⇒"; b]                     -> Impl (expandProp a, expandProp b)
  | Node [t1; Atom "="; t2]                    -> Eq   (expandTerm t1, expandTerm t2)
  | Node [Node (Atom "∀"  :: es); Atom ","; e] -> expandBinders forall es e
  | Node [Node (Atom "∃"  :: es); Atom ","; e] -> expandBinders exists es e
  | Node [Node (Atom "∃!" :: es); Atom ","; e] -> expandBinders exuniq es e
  | Node [e]                                   -> expandProp e
  | e                                          -> raise (InvalidSyntax e)

and expandBinder es0 = let (is, es) = splitWhile ((<>) (Atom ":")) es0 in
  let e = expandTerm (Node (List.tl es)) in List.map (fun i -> (expandIdent i, e)) is

and expandBinders c es e =
  let bs = List.concat (List.map (expandBinder % expandNode) es) in
  List.fold_right (fun (i, t) e0 -> c (i, t, e0)) bs (expandProp e)

type macro =
  { variables : Set.t;
    pattern   : sexp;
    value     : sexp }

let rec matchAgainst ns vbs e0 e1 = match e0, e1 with
  | Atom x,  _ when Set.mem x vbs ->
  begin match Dict.find_opt x ns with
    | Some e2 -> if e1 = e2 then Some ns else None
    | None    -> Some (Dict.add x e1 ns)
  end
  | Atom x,  Atom y when x = y     -> Some ns
  | Node xs, Node ys               ->
    if List.length xs <> List.length ys then None
    else List.fold_left2 (fun b t0 t1 -> Option.bind b (fun ns0 -> matchAgainst ns0 vbs t0 t1))
                         (Some ns) xs ys
  | _,       _                     -> None

let rec multiSubst ns = function
  | Atom x when Dict.mem x ns -> Dict.find x ns
  | Atom y                    -> Atom y
  | Node xs                   -> Node (List.map (multiSubst ns) xs)

let variables = ref Set.empty
let macros    = ref []

let rec collectVariables vbs = function
  | Atom x when Set.mem x !variables -> Set.add x vbs
  | Atom _                           -> vbs
  | Node es                          -> List.fold_left collectVariables vbs es

let rec expandDef bs = function
  | Node (Atom x :: Atom ":" :: es) -> (Atom x, (x, Node es) :: bs)
  | Node xs                         ->
    let (ys, bs') =
      List.fold_left (fun (ys, bs0) e0 ->
        let (e, bs) = expandDef bs0 e0 in
          (e :: ys, bs)) ([], bs) xs
    in (Node (List.rev ys), bs')
  | e                               -> (e, bs)

let rec findMacro e = function
  | m :: ms ->
  begin match matchAgainst Dict.empty m.variables m.pattern e with
    | None    -> findMacro e ms
    | Some ns -> Some (multiSubst ns m.value)
  end
  | []      -> None

let expandExterior e0 =
  match findMacro e0 !macros with
  | Some e -> e
  | None   -> e0

let rec macroexpand e =
  match expandExterior e with
  | Node es -> Node (List.map macroexpand es)
  | t       -> t

let rec expandProof = function
  | Atom "?"                                        -> Hole
  | Atom "trivial"                                  -> Trivial
  | Atom x                                          -> PVar (Ident.ident x)
  | Node (Atom "have" :: Atom x :: Atom ":" :: es0) -> let (t, es1) = splitWhile ((<>) (Atom "=>")) es0 in
                                                       let (e1, es2) = splitWhile ((<>) (Atom "in")) (List.tl es1) in let e2 = List.tl es2 in
                                                       Have (Ident.ident x, expandProp (macroexpand (unpack (Node t))), expandProof (Node e1), expandProof (Node e2))
  | Node [Atom "absurd"; x]                         -> Absurd (expandProof x)
  | Node [Atom "∧-intro"; a; b]                     -> Conj (expandProof a, expandProof b)
  | Node [Atom "∧-pr₁"; Atom x]                     -> Fst (Ident.ident x)
  | Node [Atom "∧-pr₂"; Atom x]                     -> Snd (Ident.ident x)
  | Node [Atom "∨-left"; x]                         -> Left (expandProof x)
  | Node [Atom "∨-right"; x]                        -> Right (expandProof x)
  | Node [Atom "∨-elim"; Atom x; a; b]              -> Disj (Ident.ident x, expandProof a, expandProof b)
  | Node (Atom "λ" :: es0)                          -> let (is, es1) = splitWhile ((<>) (Atom ",")) es0 in let e = Node (List.tl es1) in
                                                       List.fold_right (fun i e -> Lam (i, e)) (List.map expandIdent is) (expandProof e)
  | Node [Atom "∃-intro"; t; x]                     -> Exis (expandTerm (unpack t), expandProof x)
  | Node [Atom "∃-elim"; Atom x; e]                 -> ExisElim (Ident.ident x, expandProof e)
  | Node [Atom "refl"; t]                           -> Refl (expandTerm (unpack t))
  | Node [Atom "symm"; x]                           -> Symm (expandProof x)
  | Node [Atom "trans"; Atom x; Atom y]             -> Trans (Ident.ident x, Ident.ident y)
  | Node [Atom "subst"; Atom x; e1; Atom y; e2]     -> Subst (Ident.ident x, expandProp (unpack e1), Ident.ident y, expandProof e2)
  | Node [Atom "∃!-intro"; t; e1; e2]               -> ExisUniq (expandTerm (unpack t), expandProof e1, expandProof e2)
  | Node [Atom "∃!-uniq"; Atom i; e1; e2]           -> Uniq (Ident.ident i, expandProof e1, expandProof e2)
  | Node [Atom "∃!→∃"; x]                           -> Proj (expandProof x)
  | Node [Atom "lem"; e; u1; u2]                    -> Lem (expandProp (unpack e), expandProof u1, expandProof u2)
  | Node [Atom "¬¬-elim"; e]                        -> DnegElim (expandProof e)
  | Node (Atom "∀-elim" :: Atom x :: ts)            -> Inst (Ident.ident x, List.map (expandTerm % unpack) ts)
  | Node (Atom x :: y :: ys)                        -> Mp (Ident.ident x, List.map expandProof (y :: ys))
  | Node [e]                                        -> expandProof e
  | e                                               -> raise (InvalidSyntax e)
