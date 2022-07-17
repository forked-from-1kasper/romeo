open Monad
open Check
open Term

module Dict = Map.Make(String)

type sexp =
  | Atom of string
  | Node of sexp list

type command =
  | Eval      of sexp
  | Infer     of sexp
  | Postulate of string list * sexp
  | Theorem   of string * sexp * sexp
  | Axiom     of string * sexp
  | Def       of sexp * sexp
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
let keywords       = ["definition"; "theorem"; "lemma"; "proposition"; "infix";
                      "postulate"; "axiom"; "keyword";"#infer"; "#eval"; ":="]
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

let def = token "definition" >> ws >> sexpToplevel >>=
  fun e1 -> optional ws >> token ":=" >> ws >> sexpToplevel >>=
    fun e2 -> pure (Def (e1, e2))

let thm = (token "theorem" <|> token "lemma" <|> token "proposition") >> ws >> ident >>=
  fun i -> ws >> token ":" >> ws >> sexpToplevel >>=
    fun e1 -> token ":=" >> ws >> sexpToplevel >>=
      fun e2 -> pure (Theorem (i, e1, e2))

let axm = token "axiom" >> ws >> ident >>= fun i ->
  ws >> token ":" >> ws >> sexpToplevel >>= fun e ->
    pure (Axiom (i, e))

let debug ident fn = token ident >> ws >> sexpToplevel >>= fun e -> pure (fn e)

let comment = ch ';' >> str (fun c -> c <> '\n' && c <> '\r') >>= fun s -> optional ws >> pure (Comment s)

let postulate = token "postulate" >> ws >> sepBy1 ws (guard ((<>) ":") ident) << ws >>=
  fun is -> token ":" >> ws >> sexpToplevel >>= fun e -> pure (Postulate (is, e))

let infer = debug "#infer" (fun e -> Infer e)
let eval  = debug "#eval"  (fun e -> Eval e)

let cmd = optional ws >> comment <|> def <|> thm <|> postulate <|> axm <|> infer <|> eval <|> (eof >> pure Eof)

(* second stage parser *)
type associativity = Left | Right | Binder

let builtinInfix = [
  ",", (1, Binder); "=", (50, Left); "∧", (20, Right);
  "∨", (30, Right); "⊃", (40, Right); "∘", (60, Right)
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
  | Node [Node [Atom "ε"; b]; Atom ","; e]     -> let (i, t) = expandBinder b in Eps (i, t, expandProp e)
  | Node (f :: xs)                             -> List.fold_left Term.app (expandTerm f) (List.map expandTerm xs)
  | e                                          -> raise (InvalidSyntax e)
and expandProp = function
  | Atom "⊤"                                   -> True
  | Atom "⊥"                                   -> False
  | Node [a; Atom "∧"; b]                      -> And (expandProp a, expandProp b)
  | Node [a; Atom "∨"; b]                      -> Or  (expandProp a, expandProp b)
  | Node [a; Atom "⊃"; b]                      -> And (expandProp a, expandProp b)
  | Node [t1; Atom "="; t2]                    -> Eq  (expandTerm t1, expandTerm t2)
  | Node [Node (Atom "∀"  :: bs); Atom ","; e] -> expandBinders forall bs e
  | Node [Node (Atom "∃"  :: bs); Atom ","; e] -> expandBinders exists bs e
  | Node [Node (Atom "∃!" :: bs); Atom ","; e] -> expandBinders exuniq bs e
  | e                                          -> raise (InvalidSyntax e)
and expandBinder = function
  | Node [Atom i; Atom ":"; t]                 -> (Ident.ident i, expandTerm t)
  | Node (Atom i :: Atom ":" :: ts)            -> (Ident.ident i, expandTerm (Node ts))
  | e                                          -> raise (InvalidSyntax e)
and expandBinders c bs e =
  List.fold_right (fun b e0 -> let (i, t) = expandBinder b in c (i, t, e0)) bs (expandProp e)

let expandIdent = function
  | Atom x -> Ident.ident x
  | e      -> raise (ExpectedIdent e)

let rec expandProof = function
  | Atom x                                      -> PVar (Ident.ident x)
  | Node [Atom "absurd"; x]                     -> Absurd (expandProof x)
  | Node [Atom "conj"; a; b]                    -> Conj (expandProof a, expandProof b)
  | Node [Atom "fst"; Atom x]                   -> Fst (Ident.ident x)
  | Node [Atom "snd"; Atom x]                   -> Snd (Ident.ident x)
  | Node [Atom "left"; x]                       -> Left (expandProof x)
  | Node [Atom "right"; x]                      -> Right (expandProof x)
  | Node [Atom "disj"; a; b]                    -> Disj (expandProof a, expandProof b)
  | Node [Node (Atom "λ" :: is); Atom ","; e]   -> List.fold_right (fun i e -> Lam (i, e)) (List.map expandIdent is) (expandProof e)
  | Node [Atom "exis"; t; x]                    -> Exis (expandTerm t, expandProof x)
  | Node [Atom "refl"; t]                       -> Refl (expandTerm t)
  | Node [Atom "symm"; x]                       -> Symm (expandProof x)
  | Node [Atom "trans"; Atom x; Atom y]         -> Trans (Ident.ident x, Ident.ident y)
  | Node [Atom "subst"; Atom x; e1; Atom y; e2] -> Subst (Ident.ident x, expandProp e1, Ident.ident y, expandProof e2)
  | Node [Atom "choice"; Atom x]                -> Choice (Ident.ident x)
  | Node (Atom "inst" :: Atom x :: ts)          -> Inst (Ident.ident x, List.map expandTerm ts)
  | Node (Atom x :: y :: ys)                    -> Mp (Ident.ident x, List.map expandProof (y :: ys))
  | Node [e]                                    -> expandProof e
  | e                                           -> raise (InvalidSyntax e)