open Ident
open Term

type proof =
  | PVar   of ident
  | Absurd of proof                                          (* ⊥ ⊢ A *)
  | Conj   of proof * proof                           (* A, B ⊢ A ∧ B *)
  | Fst    of ident                                      (* A ∧ B ⊢ A *)
  | Snd    of ident                                      (* A ∧ B ⊢ B *)
  | Left   of proof                                      (* A ⊢ A ∨ B *)
  | Right  of proof                                      (* B ⊢ A ∨ B *)
  | Disj   of proof * proof               (* A → C, B → C ⊢ A ∨ B → C *)
  | Lam    of ident * proof                        (* (A ⊢ B) ⊢ A → B *)
  | Mp     of ident * proof                           (* A → B, A ⊢ B *)
  | Inst   of ident * term             (* ∀ (y : A), B y; x : A ⊢ B x *)
  | Exis   of term * proof                   (* x : A, P x ⊢ ∃ y, P y *)
  | Refl   of term                                           (* a = a *)
  | Symm   of proof                                  (* a = b ⊢ b = a *)
  | Trans  of ident * ident                   (* a = b, b = c ⊢ a = c *)
  | Subst  of ident * prop * ident * proof      (* a = b, P(a) ⊢ P(b) *)
  | Choice of ident                     (* H : ∃ x, P x ⊢ P(ε x, P x) *)

exception CheckError     of proof * prop
exception IneqProp       of prop * prop
exception ExpectedAnd    of prop
exception ExpectedImpl   of prop
exception ExpectedForall of prop
exception ExpectedExists of prop
exception ExpectedEq     of prop

type env =
  { term  : term Env.t;
    proof : prop Env.t }

let extAnd = function
  | And (a, b) -> (a, b)
  | e          -> raise (ExpectedAnd e)

let extImpl = function
  | Impl (a, b) -> (a, b)
  | e           -> raise (ExpectedImpl e)

let extForall = function
  | Forall c -> c
  | e        -> raise (ExpectedForall e)

let extExists = function
  | Exists c -> c
  | e        -> raise (ExpectedExists e)

let extEq = function
  | Eq (t1, t2) -> (t1, t2)
  | e           -> raise (ExpectedEq e)

let get ctx x =
  match Env.find_opt x ctx.proof with
  | None   -> raise (VariableNotFound x)
  | Some t -> t

let coincide ctx e1 e2 = if not (convProp ctx.term e1 e2) then raise (IneqProp (e1, e2))

let rec ensure ctx e t = match e, t with
  | PVar x, _ -> coincide ctx (get ctx x) t
  | Absurd u, _ -> ensure ctx u False
  | Conj (u1, u2), And (t1, t2) -> ensure ctx u1 t1; ensure ctx u2 t2
  | Fst x, b -> let (a, _) = extAnd (get ctx x) in coincide ctx a b
  | Snd x, b -> let (_, a) = extAnd (get ctx x) in coincide ctx a b
  | Left u, Or (t, _) -> ensure ctx u t
  | Right u, Or (_, t) -> ensure ctx u t
  | Disj (u1, u2), Impl (Or (a, b), c) -> ensure ctx u1 (Impl (a, c)); ensure ctx u2 (Impl (b, c))
  | Lam (x, u), Impl (a, b) -> ensure { ctx with proof = Env.add x a ctx.proof } u b
  | Lam (x, u), Forall (y, t, i) -> ensure { ctx with term = upVar ctx.term x t } u (substProp ctx.term y (Var x) i)
  | Mp (x, e), c -> let (a, b) = extImpl (get ctx x) in ensure ctx e a; coincide ctx b c
  | Inst (x, e), i1 -> let (y, t, i2) = extForall (get ctx x) in eqNf ctx.term (check ctx.term e) t; coincide ctx (substProp ctx.term y (eval ctx.term e) i1) i2
  | Exis (e, u), Exists (x, t, i) -> eqNf ctx.term (check ctx.term e) t; ensure ctx u (substProp ctx.term x (eval ctx.term e) i)
  | Refl t0, Eq (t1, t2) -> let t = eval ctx.term t0 in eqNf ctx.term t t1; eqNf ctx.term t t2
  | Symm u, Eq (t1, t2) -> ensure ctx u (Eq (t2, t1))
  | Trans (x, y), Eq (t1, t2) -> let (a, b1) = extEq (get ctx x) in let (b2, c) = extEq (get ctx y) in eqNf ctx.term b1 b2; eqNf ctx.term a t1; eqNf ctx.term c t2
  | Subst (x, e, p, u), i -> let (a, b) = extEq (get ctx p) in ensure ctx u (substProp ctx.term x a e); coincide ctx (substProp ctx.term x b e) i
  | Choice p, i2 -> let (x, t, i1) = extExists (get ctx p) in coincide ctx (substProp ctx.term x (Eps (x, t, i1)) i1) i2
  | _, _ -> raise (CheckError (e, t))