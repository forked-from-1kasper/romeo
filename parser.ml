open Monad
open Term

module Dict = Map.Make(String)

type sexp =
  | Atom of string
  | Node of sexp list

type command =
  | Def of sexp * sexp
  | Eof

let rec replace x e = function
  | Atom y  -> if x = y then e else Atom y
  | Node ys -> Node (List.map (replace x e) ys)

let rec showSExp = function
  | Node xs -> "(" ^ String.concat " " (List.map showSExp xs) ^ ")"
  | Atom s  -> s

let atom s  = Atom s
let node xs = Node xs

let ws             = str (fun c -> c = ' ' || c = '\n' || c = '\t' || c = '\t')
let keywords       = ["definition"; "theorem"; "infix"; "keyword"; ":="]
let reserved       = ['('; ')'; '\n'; '\t'; '\r'; ' ']
let isReserved   c = List.mem c reserved
let isntReserved c = not (List.mem c reserved)
let isntKeyword  s = not (List.mem s keywords)

let ident = decorateErrors ["ident"] (guard isntKeyword (str isntReserved))
let sexp = fix (fun p -> (node <$> (ch '(' >> many ws >> many p << ch ')'))
                     <|> (atom <$> ident) << many ws)

let sexpToplevel = sexp >>= fun x -> many sexp >>= fun xs ->
  pure (match xs with [] -> x | _ -> Node (x :: xs))

let def = token "definition" >> many ws >> sexpToplevel >>=
  fun e1 -> many ws >> token ":=" >> many ws >> sexpToplevel >>=
    fun e2 -> pure (Def (e1, e2))

let cmd = many ws >> def <|> (eof >> pure Eof)

type associativity = Left | Right | Binder

let builtinInfix = [
  ",", (1, Binder); "=", (50, Left); "∧", (20, Right);
  "∨", (30, Right); "⊃", (40, Right); "∘", (60, Right)
]
let operators = ref (Dict.of_seq (List.to_seq builtinInfix))

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

let rec expandTerm = function
  | Atom x                                    -> Var (Ident.ident x)
  | Node [Atom "cod"; x]                      -> Cod (expandTerm x)
  | Node [Atom "dom"; x]                      -> Dom (expandTerm x)
  | Node [Atom "id"; x]                       -> Id  (expandTerm x)
  | Node [f; Atom "∘"; g]                     -> Com (expandTerm f, expandTerm g)
  | Node [Atom "Hom"; t; a; b]                -> Hom (expandTerm t, expandTerm a, expandTerm b)
  | Node [Node [Atom "ε"; b]; Atom ","; e]    -> let (i, t) = expandBinder b in Eps (i, t, expandProp e)
  | Node (f :: xs)                            -> List.fold_left Term.app (expandTerm f) (List.map expandTerm xs)
  | e                                         -> raise (InvalidSyntax e)
and expandProp = function
  | Atom "⊤"                                  -> True
  | Atom "⊥"                                  -> False
  | Node [a; Atom "∧"; b]                     -> And (expandProp a, expandProp b)
  | Node [a; Atom "∨"; b]                     -> Or  (expandProp a, expandProp b)
  | Node [a; Atom "⊃"; b]                     -> And (expandProp a, expandProp b)
  | Node [t1; Atom "="; t2]                   -> Eq  (expandTerm t1, expandTerm t2)
  | Node [Node (Atom "∀" :: bs); Atom ","; e] -> List.fold_left (fun e0 b -> let (i, t) = expandBinder b in Forall (i, t, e0)) (expandProp e) bs
  | Node [Node (Atom "∃" :: bs); Atom ","; e] -> List.fold_left (fun e0 b -> let (i, t) = expandBinder b in Exists (i, t, e0)) (expandProp e) bs
  | e                                         -> Printf.printf "FAIL: %s\n" (showSExp e); raise (InvalidSyntax e)
and expandBinder = function
  | Node [Atom i; Atom ":"; t]      -> (Ident.ident i, expandTerm t)
  | Node (Atom i :: Atom ":" :: ts) -> (Ident.ident i, expandTerm (Node ts))
  | e                               -> raise (InvalidSyntax e)