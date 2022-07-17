open Parser
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
  | App (f, x)    -> Printf.sprintf "%s %s" (ppTerm true f) (ppTerm true x)
  | Hom (t, a, b) -> Printf.sprintf "Hom %s %s %s" (ppTerm true t) (ppTerm true a) (ppTerm true b)
  | Eps (i, t, e) -> Printf.sprintf "ε (%s : %s), %s" (showIdent i) (showTerm t) (showProp e)
  in match t with U _ | Var _ -> s | _ -> parens paren s

and ppProp paren e =
  let s = match e with
  | True             -> "⊤"
  | False            -> "⊥"
  | And (a, b)       -> Printf.sprintf "%s ∧ %s" (ppProp true a) (showProp b)
  | Or (a, b)        -> Printf.sprintf "%s ∨ %s" (ppProp true a) (showProp b)
  | Impl (a, b)      -> Printf.sprintf "%s ⊃ %s" (ppProp true a) (showProp b)
  | Eq (t1, t2)      -> Printf.sprintf "%s = %s" (showTerm t1) (showTerm t2)
  | Forall (i, t, e) -> Printf.sprintf "∀ (%s : %s), %s"  (showIdent i) (showTerm t) (showProp e)
  | Exists (i, t, e) -> Printf.sprintf "∃ (%s : %s), %s"  (showIdent i) (showTerm t) (showProp e)
  | ExUniq (i, t, e) -> Printf.sprintf "∃! (%s : %s), %s" (showIdent i) (showTerm t) (showProp e)
  in match e with True | False -> s | _ -> parens paren s

and showTerm t = ppTerm false t
and showProp e = ppProp false e

let rec ppProof paren e =
  let s = match e with
  | Hole                -> "?"
  | PVar x              -> showIdent x
  | Absurd e            -> "absurd " ^ ppProof true e
  | Have (x, t, e1, e2) -> Printf.sprintf "let %s : %s => %s in %s" (showIdent x) (showProp t) (showProof e1) (showProof e2)
  | Conj (e1, e2)       -> Printf.sprintf "conj %s %s" (ppProof true e1) (ppProof true e2)
  | Fst x               -> "fst " ^ showIdent x
  | Snd x               -> "snd " ^ showIdent x
  | Left e              -> "left " ^ ppProof true e
  | Right e             -> "right " ^ ppProof true e
  | Disj (e1, e2)       -> Printf.sprintf "disj %s %s" (ppProof true e1) (ppProof true e2)
  | Lam (x, e)          -> Printf.sprintf "λ %s, %s" (showIdent x) (showProof e)
  | Mp (x, es)          -> Printf.sprintf "%s %s" (showIdent x) (String.concat " " (List.map (ppProof true) es))
  | Inst (x, ts)        -> Printf.sprintf "inst %s %s" (showIdent x) (String.concat " " (List.map (ppTerm true) ts))
  | Exis (t, e)         -> Printf.sprintf "exis %s %s" (ppTerm true t) (ppProof true e)
  | Refl t              -> "refl " ^ ppTerm true t
  | Symm e              -> "symm " ^ ppProof true e
  | Trans (x, y)        -> Printf.sprintf "trans %s %s" (showIdent x) (showIdent y)
  | Subst (x, e, p, u)  -> Printf.sprintf "subst %s %s %s %s" (showIdent x) (ppProp true e) (showIdent p) (ppProof true u)
  | Choice x            -> "choice " ^ showIdent x
  in match e with Hole | PVar _ -> s | _ -> parens paren s

and showProof e = ppProof true e

let showError = function
  | VariableNotFound x -> Printf.sprintf "Unbound variable “%s”." (showIdent x)
  | ExpectedUniv t     -> Printf.sprintf "“%s” expected to be a universe." (showTerm t)
  | ExpectedHom t      -> Printf.sprintf "“%s” expected to be Hom." (showTerm t)
  | Ineq (t1, t2)      -> Printf.sprintf "%s\n  ≠\n%s" (showTerm t1) (showTerm t2)
  | InvalidSyntax stx  -> Printf.sprintf "Invalid syntax:\n%s\n" (showSExp stx)
  | CheckError (e, t)  -> Printf.sprintf "Cannot check “%s” against “%s”." (showProof e) (showProp t)
  | IneqProp (e1, e2)  -> Printf.sprintf "%s\n  ≠\n%s" (showProp e1) (showProp e2)
  | ex                 -> Printf.sprintf "Uncaught exception: %s" (Printexc.to_string ex)