open Monad
open Term

module Dict = Map.Make(String)
module Set  = Set.Make(String)

type associativity = Left | Right | Binder

type sexp =
  | Atom of string
  | Node of sexp list

type command =
  | Eval      of sexp
  | Infer     of sexp
  | Postulate of string list * sexp
  | Theorem   of string * sexp * sexp
  | Axiom     of string * sexp
  | Macro     of sexp * sexp
  | Def       of sexp * sexp
  | Infix     of associativity * int * string list
  | Variables of string list
  | Comment   of string
  | Eof

let rec replace x e = function
  | Atom y  -> if x = y then e else Atom y
  | Node ys -> Node (List.map (replace x e) ys)

let rec showSExp = function
  | Node xs -> "(" ^ String.concat " " (List.map showSExp xs) ^ ")"
  | Atom s  -> s

let atom s  = Atom s
let node xs = Node xs

(* first stage parser *)
let numSubscript =
  ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"]
  |> List.mapi (fun idx s -> token s >> pure idx)
  |> List.fold_left (<|>) failure

let digits ns = let deg = ref 1 in let m = ref 0 in
  List.iter (fun d -> m := !m + d * !deg; deg := !deg * 10) (List.rev ns); !m

let universe = digits <$> (ch 'U' >> many numSubscript)

let ws             = str (fun c -> c = ' ' || c = '\n' || c = '\t' || c = '\t') >> Monad.eps
let keywords       = ["definition"; "macro"; "theorem"; "lemma"; "proposition";
                      "infixl"; "infixr"; "postulate"; "axiom"; "NB"; "variables";
                      "#infer"; "#eval"; ":="]
let reserved       = ['('; ')'; '\n'; '\t'; '\r'; ' '; ',']
let isReserved   c = List.mem c reserved
let isntReserved c = not (List.mem c reserved)
let isntKeyword  s = not (List.mem s keywords)

let ident = decorateErrors ["ident"] (guard isntKeyword (str isntReserved))
let sexp = fix (fun p -> (node <$> (ch '(' >> optional ws >> many p << ch ')'))
                     <|> (ch ',' >> pure (Atom ","))
                     <|> (atom <$> ident) << optional ws)

let sexpToplevel = sexp >>= fun x -> many sexp >>= fun xs ->
  pure (match xs with [] -> x | _ -> Node (x :: xs))

let macrodef tok = token tok >> ws >> sexpToplevel >>=
  fun e1 -> optional ws >> token ":=" >> ws >> sexpToplevel >>=
    fun e2 -> pure (e1, e2)

let def   = macrodef "definition" >>= fun (e1, e2) -> pure (Def (e1, e2))
let macro = macrodef "macro"      >>= fun (e1, e2) -> pure (Macro (e1, e2))

let thm = (token "theorem" <|> token "lemma" <|> token "proposition") >> ws >> ident >>=
  fun i -> ws >> token ":" >> ws >> sexpToplevel >>=
    fun e1 -> token ":=" >> ws >> sexpToplevel >>=
      fun e2 -> pure (Theorem (i, e1, e2))

let axm = token "axiom" >> ws >> ident >>= fun i ->
  ws >> token ":" >> ws >> sexpToplevel >>= fun e ->
    pure (Axiom (i, e))

let infix assoc tok = token tok >> ws >> ident << ws >>= fun e ->
  sepBy1 ws ident >>= fun is -> pure (Infix (assoc, int_of_string e, is))

let infixl = infix Left  "infixl"
let infixr = infix Right "infixr"

let debug ident fn = token ident >> ws >> sexpToplevel >>= fun e -> pure (fn e)

let comment = token "NB" >> ws >> str (fun c -> c <> '\n' && c <> '\r') >>= fun s -> optional ws >> pure (Comment s)

let postulate = token "postulate" >> ws >> sepBy1 ws (guard ((<>) ":") ident) << ws >>=
  fun is -> token ":" >> ws >> sexpToplevel >>= fun e -> pure (Postulate (is, e))

let infer = debug "#infer" (fun e -> Infer e)
let eval  = debug "#eval"  (fun e -> Eval e)

let variables = token "variables" >> ws >> sepBy1 ws ident >>= fun is -> pure (Variables is)

let cmdeof = eof >> pure Eof

let cmdline = comment   <|> def   <|> macro <|> thm    <|> postulate
          <|> axm       <|> infer <|> eval  <|> infixr <|> infixl
          <|> variables <|> cmdeof

let cmd = optional ws >> cmdline

(* second stage parser *)
let builtinInfix = [
  ",", (1, Binder); "=", (50, Left); "∧", (20, Right); "∨", (30, Right);
  "⊃", (40, Right); "⇒", (40, Right); "∘", (60, Right)
]
let operators = ref (Dict.of_seq (List.to_seq builtinInfix))

(* From: https://rosettacode.org/wiki/Parsing/Shunting-yard_algorithm#OCaml *)
let splitWhile p =
  let rec go ls = function
    | x :: xs when p x -> go (x :: ls) xs
    | xs               -> List.rev ls, xs
  in go []

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
      in pusher (Atom op :: stack') [] (mv @ unbuf buf :: queue) xs
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

exception InvalidSyntax of sexp
exception ExpectedIdent of sexp
exception ExpectedNode  of sexp

let rec ofNat n = if n <= 0 then Zero else Succ (ofNat (n - 1))

let expandVar x =
  match runParser universe (ofString x) 0 with
  | Ok (_, n) -> U (ofNat n)
  | Error _   -> Var (Ident.ident x)

let expandIdent = function
  | Atom x -> Ident.ident x
  | e      -> raise (ExpectedIdent e)

let expandNode = function
  | Node es -> es
  | e       -> raise (ExpectedNode e)

let rec expandTerm = function
  | Atom x                                     -> expandVar x
  | Node [Atom "cod"; x]                       -> Cod (expandTerm x)
  | Node [Atom "dom"; x]                       -> Dom (expandTerm x)
  | Node [Atom "id"; x]                        -> Id  (expandTerm x)
  | Node [f; Atom "∘"; g]                      -> Com (expandTerm f, expandTerm g)
  | Node [Atom "Hom"; t; a; b]                 -> Hom (expandTerm t, expandTerm a, expandTerm b)
  | Node [Node [Atom "ε"; b]; Atom ","; e]     -> let (i, t) = expandEpsBinder b in Eps (i, t, expandProp e)
  | Node (f :: xs)                             -> List.fold_left Term.app (expandTerm f) (List.map expandTerm xs)
  | e                                          -> raise (InvalidSyntax e)

and expandEpsBinder = function
  | Node (Atom i :: Atom ":" :: ts) -> Ident.ident i, expandTerm (Node ts)
  | e                               -> raise (InvalidSyntax e)

and expandProp = function
  | Atom "⊤"                                   -> True
  | Atom "⊥"                                   -> False
  | Node [a; Atom "∧"; b]                      -> And  (expandProp a, expandProp b)
  | Node [a; Atom "∨"; b]                      -> Or   (expandProp a, expandProp b)
  | Node [a; Atom "⊃"; b]                      -> Impl (expandProp a, expandProp b)
  | Node [a; Atom "⇒"; b]                     -> Impl (expandProp a, expandProp b)
  | Node [t1; Atom "="; t2]                    -> Eq   (expandTerm t1, expandTerm t2)
  | Node [Node (Atom "∀"  :: es); Atom ","; e] -> expandBinders forall es e
  | Node [Node (Atom "∃"  :: es); Atom ","; e] -> expandBinders exists es e
  | Node [Node (Atom "∃!" :: es); Atom ","; e] -> expandBinders exuniq es e
  | e                                          -> raise (InvalidSyntax e)

and expandBinder es0 = let (is, es) = splitWhile ((<>) (Atom ":")) es0 in
  let e = expandTerm (Node (List.tl es)) in List.map (fun i -> (expandIdent i, e)) is

and expandBinders c es e =
  let bs = List.concat (List.map (expandBinder % expandNode) es) in
  List.fold_right (fun (i, t) e0 -> c (i, t, e0)) bs (expandProp e)

let rec expandProof = function
  | Atom "?"                                        -> Hole
  | Atom x                                          -> PVar (Ident.ident x)
  | Node (Atom "have" :: Atom x :: Atom ":" :: es0) -> let (t, es1) = splitWhile ((<>) (Atom "=>")) es0 in
                                                       let (e1, es2) = splitWhile ((<>) (Atom "in")) (List.tl es1) in let e2 = List.tl es2 in
                                                       Have (Ident.ident x, expandProp (unpack (Node t)), expandProof (Node e1), expandProof (Node e2))
  | Node [Atom "absurd"; x]                         -> Absurd (expandProof x)
  | Node [Atom "conj"; a; b]                        -> Conj (expandProof a, expandProof b)
  | Node [Atom "fst"; Atom x]                       -> Fst (Ident.ident x)
  | Node [Atom "snd"; Atom x]                       -> Snd (Ident.ident x)
  | Node [Atom "left"; x]                           -> Left (expandProof x)
  | Node [Atom "right"; x]                          -> Right (expandProof x)
  | Node [Atom "disj"; a; b]                        -> Disj (expandProof a, expandProof b)
  | Node (Atom "λ" :: es0)                          -> let (is, es1) = splitWhile ((<>) (Atom ",")) es0 in let e = Node (List.tl es1) in
                                                       List.fold_right (fun i e -> Lam (i, e)) (List.map expandIdent is) (expandProof e)
  | Node [Atom "exis"; t; x]                        -> Exis (expandTerm (unpack t), expandProof x)
  | Node [Atom "refl"; t]                           -> Refl (expandTerm (unpack t))
  | Node [Atom "symm"; x]                           -> Symm (expandProof x)
  | Node [Atom "trans"; Atom x; Atom y]             -> Trans (Ident.ident x, Ident.ident y)
  | Node [Atom "subst"; Atom x; e1; Atom y; e2]     -> Subst (Ident.ident x, expandProp (unpack e1), Ident.ident y, expandProof e2)
  | Node [Atom "choice"; Atom x]                    -> Choice (Ident.ident x)
  | Node [Atom "exisUniq"; t; e1; e2]               -> ExisUniq (expandTerm (unpack t), expandProof e1, expandProof e2)
  | Node [Atom "uniq"; Atom i; e1; e2]              -> Uniq (Ident.ident i, expandProof e1, expandProof e2)
  | Node [Atom "proj"; x]                           -> Proj (expandProof x)
  | Node (Atom "inst" :: Atom x :: ts)              -> Inst (Ident.ident x, List.map (expandTerm % unpack) ts)
  | Node (Atom x :: y :: ys)                        -> Mp (Ident.ident x, List.map expandProof (y :: ys))
  | Node [e]                                        -> expandProof e
  | e                                               -> raise (InvalidSyntax e)

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
