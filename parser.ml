open Monad

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