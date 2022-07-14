open Monad

type sexp =
  | Atom of string
  | Node of sexp list

let rec showSExp = function
  | Node xs -> "(" ^ String.concat " " (List.map showSExp xs) ^ ")"
  | Atom s  -> s

let atom s  = Atom s
let node xs = Node xs

let ws       = str (fun c -> c = ' ' || c = '\n' || c = '\t' || c = '\t')
let reserved = ['('; ')'; ':'; '\n'; '\t'; '\r'; ' ']
let ident    = str (fun c -> not (List.mem c reserved))
               |> decorateErrors ["ident"]

let sexp = fix (fun p -> (atom <$> (ident << many ws))
                     <|> (node <$> (ch '(' >> many p << ch ')' << many ws)))