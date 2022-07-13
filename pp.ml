open Ident
open Term

let rec toInt64 = function
  | Zero   -> 0L
  | Succ n -> Int64.add (toInt64 n) 1L

let showIdent (s, _) = s
let parens b x = if b then "(" ^ x ^ ")" else x

let rec ppTerm paren t =
  let s = match t with
  | U n           -> "U" ^ showSubscript (toInt64 n)
  | Var x         -> showIdent x
  | Dom g         -> "dom " ^ ppTerm true g
  | Cod g         -> "cod " ^ ppTerm true g
  | Id x          -> "id " ^ ppTerm true x
  | Com (g, f)    -> Printf.sprintf "%s ∘ %s" (showTerm g) (showTerm f)
  | App (f, x)    -> Printf.sprintf "%s %s" (showTerm f) (ppTerm true x)
  | Hom (t, a, b) -> Printf.sprintf "Hom %s %s %s" (ppTerm true t) (ppTerm true a) (ppTerm true b)
  | Eps (i, t, e) -> Printf.sprintf "ε (%s : %s), %s" (showIdent i) (showTerm t) (showProp e)
  in match t with U _ | Var _ -> s | _ -> parens paren s

and ppProp paren e =
  let s = match e with
  | True             -> "⊤"
  | False            -> "⊥"
  | And (a, b)       -> Printf.sprintf "%s ∧ %s" (ppProp true a) (showProp b)
  | Or (a, b)        -> Printf.sprintf "%s ∨ %s" (ppProp true a) (showProp b)
  | Impl (a, b)      -> Printf.sprintf "%s → %s" (ppProp true a) (showProp b)
  | Eq (t1, t2)      -> Printf.sprintf "%s = %s" (showTerm t1) (showTerm t2)
  | Forall (i, t, e) -> Printf.sprintf "∀ (%s : %s), %s" (showIdent i) (showTerm t) (showProp e)
  | Exists (i, t, e) -> Printf.sprintf "∃ (%s : %s), %s" (showIdent i) (showTerm t) (showProp e)
  in match e with True | False -> s | _ -> parens paren s

and showTerm t = ppTerm false t
and showProp e = ppProp false e