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
  | Const (x, []) -> showIdent x
  | Const (x, ts) -> showIdent x ^ "[" ^ String.concat ", " (List.map showTerm ts) ^ "]"
  | Dom g         -> "dom " ^ ppTerm true g
  | Cod g         -> "cod " ^ ppTerm true g
  | Id x          -> "id " ^ ppTerm true x
  | Com (g, f)    -> Printf.sprintf "%s ∘ %s" (showTerm g) (showTerm f)
  | App (f, x)    -> Printf.sprintf "%s %s" (ppTerm true f) (ppTerm true x)
  | Hom (t, a, b) -> Printf.sprintf "Hom %s %s %s" (ppTerm true t) (ppTerm true a) (ppTerm true b)
  in match t with U _ | Var _ -> s | _ -> parens paren s
and showTerm t = ppTerm false t

let rec ppProp paren e =
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
and showProp e = ppProp false e

let showCtx show ctx =
  Env.bindings ctx.local
  |> List.map (fun (x, e) -> Printf.sprintf "%s : %s" (showIdent x) (show e))
  |> String.concat "\n"

let rec ppProof paren e =
  let s = match e with
  | Hole                 -> "?"
  | Trivial              -> "trivial"
  | PVar x               -> showIdent x
  | Absurd e             -> "absurd " ^ ppProof true e
  | Have (x, t, e1, e2)  -> Printf.sprintf "let %s : %s => %s in %s" (showIdent x) (showProp t) (showProof e1) (showProof e2)
  | Conj (e1, e2)        -> Printf.sprintf "∧-intro %s %s" (ppProof true e1) (ppProof true e2)
  | Fst x                -> "∧-pr₁ " ^ showIdent x
  | Snd x                -> "∧-pr₂ " ^ showIdent x
  | Left e               -> "∨-left " ^ ppProof true e
  | Right e              -> "∨-right " ^ ppProof true e
  | Disj (e1, e2)        -> Printf.sprintf "∨-elim %s %s" (ppProof true e1) (ppProof true e2)
  | Lam (x, e)           -> Printf.sprintf "λ %s, %s" (showIdent x) (showProof e)
  | Mp (x, es)           -> Printf.sprintf "%s %s" (showIdent x) (String.concat " " (List.map (ppProof true) es))
  | Inst (x, ts)         -> Printf.sprintf "∀-elim %s %s" (showIdent x) (String.concat " " (List.map (ppTerm true) ts))
  | Exis (t, e)          -> Printf.sprintf "∃-intro %s %s" (ppTerm true t) (ppProof true e)
  | ExisElim (x, e)      -> Printf.sprintf "∃-elim %s %s" (showIdent x) (ppProof true e)
  | Refl t               -> "refl " ^ ppTerm true t
  | Symm e               -> "symm " ^ ppProof true e
  | Trans (x, y)         -> Printf.sprintf "trans %s %s" (showIdent x) (showIdent y)
  | Subst (x, e, p, u)   -> Printf.sprintf "subst %s %s %s %s" (showIdent x) (ppProp true e) (showIdent p) (ppProof true u)
  | ExisUniq (t, e1, e2) -> Printf.sprintf "∃!-intro %s %s %s" (ppTerm true t) (ppProof true e1) (ppProof true e2)
  | Uniq (i, e1, e2)     -> Printf.sprintf "∃!-uniq %s %s %s" (showIdent i) (ppProof true e1) (ppProof true e2)
  | Proj e               -> "∃!→∃ " ^ ppProof true e
  | Lem (e, u1, u2)      -> Printf.sprintf "lem %s %s %s" (ppProp true e) (ppProof true u1) (ppProof true u2)
  | DnegElim e           -> "¬¬-elim " ^ ppProof true e
  in match e with Hole | PVar _ -> s | _ -> parens paren s

and showProof e = ppProof false e

let typeMismatch = Printf.sprintf "Type mismatch:\n  %s\nis not equal to\n  %s"

let showError = function
  | VariableAlreadyDeclared x -> Printf.sprintf "Variable “%s” is already declared." (showIdent x)
  | VariableNotFound x        -> Printf.sprintf "Unbound variable “%s”." (showIdent x)
  | InvalidArity (i, n, m)    -> Printf.sprintf "Constant “%s” expects %d argument(s), while %d given." (showIdent i) n m
  | ExpectedUniv t            -> Printf.sprintf "“%s” expected to be a universe." (showTerm t)
  | ExpectedHom t             -> Printf.sprintf "“%s” expected to be Hom." (showTerm t)
  | ExpectedAnd e             -> Printf.sprintf "“%s” expected to be a conjunction." (showProp e)
  | ExpectedImpl e            -> Printf.sprintf "“%s” expected to be an implication." (showProp e)
  | ExpectedForall e          -> Printf.sprintf "“%s” expected to be an universal quantifier." (showProp e)
  | ExpectedExists e          -> Printf.sprintf "“%s” expected to be an existential quantifier." (showProp e)
  | ExpectedExUniq e          -> Printf.sprintf "“%s” expected to be ∃! quantifier." (showProp e)
  | ExpectedEq e              -> Printf.sprintf "“%s” expected to be an equality." (showProp e)
  | ExpectedIdent e           -> Printf.sprintf "“%s” expected to be an ident." (showSExp e)
  | ExpectedNode e            -> Printf.sprintf "“%s” expected to be a node." (showSExp e)
  | Ineq (t1, t2)             -> typeMismatch (showTerm t1) (showTerm t2)
  | IneqProp (e1, e2)         -> typeMismatch (showProp e1) (showProp e2)
  | InvalidSyntax stx         -> Printf.sprintf "Invalid syntax:\n  %s\n" (showSExp stx)
  | CheckError (e, t)         -> Printf.sprintf "Cannot check\n  %s\nagainst\n  %s" (showProof e) (showProp t)
  | ex                        -> Printf.sprintf "Uncaught exception: %s" (Printexc.to_string ex)