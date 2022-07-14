(* https://github.com/leanprover-community/lean/blob/master/library/data/buffer/parser.lean *)

let (%) f g = fun x -> f (g x)

type 'a parserResult =
  | Done of int * 'a
  | Fail of int * string list

type reader =
  { get  : int -> char;
    size : int }

type 'a parser = reader -> int -> 'a parserResult

let pure a = fun _ pos -> Done (pos, a)

let (>>=) x f =
  fun input pos -> match x input pos with
  | Done (pos, a)        -> f a input pos
  | Fail (pos, expected) -> Fail (pos, expected)

let (>>) x y  = x >>= fun _ -> y
let (<<) x y  = x >>= fun r -> y >>= fun _ -> pure r
let (<$>) f x = x >>= fun y -> pure (f y)
let (<*>) p q = p >>= fun f -> q >>= fun x -> pure (f x)

let fail msg = fun _ pos -> Fail (pos, [msg])
let failure  = fun _ pos -> Fail (pos, [])

let (<|>) p q = fun input pos ->
  match p input pos with
  | Fail (pos1, expected1) ->
    if pos1 <> pos then Fail (pos1, expected1) else
    begin match q input pos with
    | Fail (pos2, expected2) ->
      if pos1 < pos2 then
        Fail (pos1, expected1)
      else if pos2 < pos1 then
        Fail (pos2, expected2)
      else Fail (pos1, List.append expected1 expected2)
    | ok -> ok
    end
  | ok -> ok

let decorateErrors msgs p =
  fun input pos -> match p input pos with
  | Fail _ -> Fail (pos, msgs)
  | ok     -> ok

let anyChar : char parser =
  fun input pos ->
    if pos < input.size then
      Done (pos + 1, input.get pos)
    else Fail (pos, [])

let sat p : char parser =
  fun input pos ->
    if pos < input.size then
      let c = input.get pos in
      if p c then Done (pos + 1, c) else Fail (pos, [])
    else Fail (pos, [])

let eps = pure ()

let ch c = sat ((=) c) >> eps |> decorateErrors [String.make 1 c]
let token s =
  Seq.fold_left (fun x c -> x >> ch c) eps (String.to_seq s)
  |> decorateErrors [s]

let foldr f p b =
  let rec loop reps = if reps = 0 then failure else (f <$> p <*> loop (reps - 1)) <|> pure b
  in fun input pos -> loop (input.size - pos + 1) input pos

let fix f =
  let rec loop reps = if reps = 0 then failure else f (loop (reps - 1))
  in fun input pos -> loop (input.size - pos + 1) input pos

let many  p = foldr List.cons p []
let many1 p = List.cons <$> p <*> many p

let sepBy1 sep p = List.cons <$> p <*> many (sep >> p)
let sepBy  sep p = sepBy1 sep p <|> pure []

let str p = (String.of_seq % List.to_seq) <$> many1 (sat p)

let makeMonospaced = function
  | '\n' -> ' '
  | '\t' -> ' '
  | '\r' -> ' '
  | c    -> c

let mkErrorMsg input pos expected = let width = 10 in
    String.init (2 * width + 1) (fun idx -> makeMonospaced (input.get (pos - width + idx)))
  ^ "\n" ^ String.make width ' ' ^ "^\n" ^ "expected: " ^ String.concat " | " expected

let runParser p input = match p input 0 with
  | Done (pos, r)        -> Ok (pos, r)
  | Fail (pos, expected) -> Error (mkErrorMsg input pos expected)

let ofString s : reader =
  { size = String.length s;
    get  = fun n -> if n < 0 || n >= String.length s then ' '
                    else String.get s n }

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