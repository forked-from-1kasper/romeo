open Ident
open Eval
open Term

let rec check ctx = function
  | U n           -> U (Succ n)
  | Var x         -> lookup ctx x
  | Dom g | Cod g -> let (t, _, _) = extHom (check ctx g) in t
  | Id x          -> Hom (check ctx x, x, x)
  | Com (g, f)    -> let (t1, b1, c) = extHom (check ctx g) in
                     let (t2, a, b2) = extHom (check ctx f) in
                     eqNf ctx t1 t2; eqNf ctx b1 b2; Hom (t1, a, c)
  | App (f, x)    -> checkAp ctx f x
  | Hom (t, a, b) -> let c = check ctx t in ignore (extUniv c);
                     eqNf ctx t (infer ctx a); eqNf ctx t (infer ctx b);
                     U (extUniv c)
  | Eps (x, t, e) -> ignore (extUniv (check ctx t)); checkProp (upVar ctx x t) e; t

and checkAp ctx f x = match check ctx f, check ctx x with
  | Hom (U _, c1, c2), Hom (c, a, b) when conv ctx c c1 -> Hom (c2, evalApp ctx f a, evalApp ctx f b)
  | Hom (U _, c1, c2), c                                -> eqNf ctx c c1; c2
  | t,                 _                                -> raise (ExpectedUniv t)

and checkProp ctx = function
  | True          -> ()
  | False         -> ()
  | And (a, b)    -> checkProp2 ctx a b
  | Or (a, b)     -> checkProp2 ctx a b
  | Impl (a, b)   -> checkProp2 ctx a b
  | Eq (t1, t2)   -> eqNf ctx (check ctx t1) (check ctx t2)
  | Forall c      -> checkClos ctx c
  | Exists c      -> checkClos ctx c
  | ExUniq c      -> checkClos ctx c

and checkProp2 ctx e1 e2 =
  checkProp ctx e1; checkProp ctx e2

and checkClos ctx (x, t, e) =
  ignore (extUniv (check ctx t)); checkProp (upVar ctx x t) e

type env =
  { term  : term Env.t;
    proof : prop Env.t }

let get ctx x =
  match Env.find_opt x ctx.proof with
  | None   -> raise (VariableNotFound x)
  | Some t -> t

let coincide ctx e1 e2 = if not (convProp ctx.term e1 e2) then raise (IneqProp (e1, e2))

let rec ensure ctx e t = match e, t with
  | Hole,                 _                   -> Printf.printf "Hole:\n%s\n" (Pp.showProp t)
  | PVar x,               _                   -> coincide ctx (get ctx x) t
  | Have (x, t1, e1, e2), t2                  -> ensure ctx e1 t1; ensure { ctx with proof = Env.add x t1 ctx.proof } e2 t2
  | Absurd u,             _                   -> ensure ctx u False
  | Conj (u1, u2),        And (t1, t2)        -> ensure ctx u1 t1; ensure ctx u2 t2
  | Fst x,                b                   -> let (a, _) = extAnd (get ctx x) in coincide ctx a b
  | Snd x,                b                   -> let (_, a) = extAnd (get ctx x) in coincide ctx a b
  | Left u,               Or (t, _)           -> ensure ctx u t
  | Right u,              Or (_, t)           -> ensure ctx u t
  | Disj (u1, u2),        Impl (Or (a, b), c) -> ensure ctx u1 (Impl (a, c)); ensure ctx u2 (Impl (b, c))
  | Lam (x, u),           Impl (a, b)         -> ensure { ctx with proof = Env.add x a ctx.proof } u b
  | Lam (x, u),           Forall (y, t, i)    -> ensure { ctx with term = upVar ctx.term x t } u (substProp ctx.term y (Var x) i)
  | Mp (x, es),           c0                  -> let c = List.fold_left (fun t e -> let (a, b) = extImpl t in ensure ctx e a; b) (get ctx x) es in coincide ctx c c0
  | Inst (x, ts),         c0                  -> let c = List.fold_left (fun t0 e -> let (y, t, i) = extForall t0 in eqNf ctx.term (check ctx.term e) t;
                                                                                     substProp ctx.term y (eval ctx.term e) i) (get ctx x) ts in
                                                 coincide ctx c c0
  | Exis (e, u),          Exists (x, t, i)    -> eqNf ctx.term (check ctx.term e) t; ensure ctx u (substProp ctx.term x (eval ctx.term e) i)
  | Refl t0,              Eq (t1, t2)         -> let t = eval ctx.term t0 in eqNf ctx.term t t1; eqNf ctx.term t t2
  | Symm u,               Eq (t1, t2)         -> ensure ctx u (Eq (t2, t1))
  | Trans (x, y),         Eq (t1, t2)         -> let (a, b1) = extEq (get ctx x) in let (b2, c) = extEq (get ctx y) in eqNf ctx.term b1 b2; eqNf ctx.term a t1; eqNf ctx.term c t2
  | Subst (x, e, p, u),   i                   -> let (a, b) = extEq (get ctx p) in ensure ctx u (substProp ctx.term x a e); coincide ctx (substProp ctx.term x b e) i
  | Choice p,             i2                  -> let (x, t, i1) = extExists (get ctx p) in coincide ctx (substProp ctx.term x (Eps (x, t, i1)) i1) i2
  | Proj u,               Exists (x, t, i)    -> ensure ctx u (ExUniq (x, t, i))
  | ExisUniq (e, u1, u2), ExUniq (x, t, i)    -> eqNf ctx.term (check ctx.term e) t; ensure ctx u1 (substProp ctx.term x (eval ctx.term e) i);
                                                 let y = freshName "σ" in let ctx' = upVar ctx.term y t in
                                                 ensure ctx u2 (Forall (y, t, Impl (substProp ctx' x (Var y) i, Eq (e, Var y))))
  | Uniq (i, e1, e2),     Eq (t1, t2)         -> let (x, t, e) = extExUniq (get ctx i) in
                                                 eqNf ctx.term (check ctx.term t1) t;
                                                 eqNf ctx.term (check ctx.term t2) t;
                                                 ensure ctx e1 (substProp ctx.term x t1 e);
                                                 ensure ctx e2 (substProp ctx.term x t2 e)
  | _,                        _               -> raise (CheckError (e, t))