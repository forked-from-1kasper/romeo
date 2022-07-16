open Ident

type nat =
  | Zero
  | Succ of nat

type term =
  | U      of nat
  | Var    of ident
  | Dom    of term
  | Cod    of term
  | Id     of term
  | Com    of term * term
  | App    of term * term
  | Hom    of term * term * term
  | Eps    of clos

and prop =
  | True
  | False
  | And    of prop * prop
  | Or     of prop * prop
  | Impl   of prop * prop
  | Eq     of term * term
  | Forall of clos
  | Exists of clos

and clos = ident * term * prop

let eps    (x, t, i) = Eps    (x, t, i)
let forall (x, t, i) = Forall (x, t, i)
let exists (x, t, i) = Exists (x, t, i)
let app f x          = App    (f, x)

let freshTerm x = Var (freshName x)

exception VariableNotFound of ident
exception ExpectedUniv     of term
exception ExpectedHom      of term
exception Ineq             of term * term

type ctx = term Env.t

let upVar ctx x t = Env.add x t ctx

let lookup ctx x =
  match Env.find_opt x ctx with
  | None   -> raise (VariableNotFound x)
  | Some t -> t

let extUniv = function
  | U n -> n
  | t   -> raise (ExpectedUniv t)

let extHom = function
  | Hom (t, a, b) -> (t, a, b)
  | t             -> raise (ExpectedHom t)

let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n

let rec salt ns = function
  | U n              -> U n
  | Var x            -> Var (freshVar ns x)
  | Dom g            -> Dom (salt ns g)
  | Cod g            -> Cod (salt ns g)
  | Id x             -> Id (salt ns x)
  | Com (g, f)       -> Com (salt ns g, salt ns f)
  | App (f, x)       -> App (salt ns f, salt ns x)
  | Hom (t, a, b)    -> Hom (salt ns t, salt ns a, salt ns b)
  | Eps (x, t, e)    -> let y = fresh x in Eps (x, salt ns t, saltProp (Env.add x y ns) e)

and saltProp ns = function
  | True             -> True
  | False            -> False
  | And (a, b)       -> And (saltProp ns a, saltProp ns b)
  | Or (a, b)        -> Or (saltProp ns a, saltProp ns b)
  | Impl (a, b)      -> Impl (saltProp ns a, saltProp ns b)
  | Eq (t1, t2)      -> Eq (salt ns t1, salt ns t2)
  | Forall (x, t, e) -> let y = fresh x in Forall (x, salt ns t, saltProp (Env.add x y ns) e)
  | Exists (x, t, e) -> let y = fresh x in Exists (x, salt ns t, saltProp (Env.add x y ns) e)

let rec infer ctx = function
  | U n           -> U (Succ n)
  | Var x         -> lookup ctx x
  | Dom g | Cod g -> let (t, _, _) = extHom (infer ctx g) in t
  | Id x          -> Hom (infer ctx x, x, x)
  | Com (g, f)    -> let (t, _, c) = extHom (infer ctx g) in
                     let (_, a, _) = extHom (infer ctx f) in
                     Hom (t, a, c)
  | App (f, x)    -> inferAp ctx f x
  | Hom (t, _, _) -> U (extUniv (infer ctx t))
  | Eps (_, t, _) -> t

and inferAp ctx f x =
  let (_, _, c) = extHom (infer ctx f) in
  match infer ctx x with
  | Hom (_, a, b) -> Hom (c, evalApp f a, evalApp f b)
  | _             -> c

and eval ctx = function
  | U n           -> U n
  | Var x         -> Var x
  | Dom g         -> dom ctx g
  | Cod g         -> cod ctx g
  | Id x          -> Id (eval ctx x)
  | Com (f, g)    -> com (eval ctx f) (eval ctx g)
  | App (f, x)    -> evalApp (eval ctx f) (eval ctx x)
  | Hom (t, a, b) -> Hom (eval ctx t, eval ctx a, eval ctx b)
  | Eps (x, t, e) -> let t' = eval ctx t in Eps (x, t', evalProp (upVar ctx x t') e)

and dom ctx g = let (_, t, _) = extHom (infer ctx g) in t
and cod ctx g = let (_, _, t) = extHom (infer ctx g) in t

and com f g = match f, g with
  | Com (g, h), f -> com g (com h f)
  | Id _, f       -> f
  | f, Id _       -> f
  | f, g          -> Com (f, g)

and evalApp f x = match f, x with
  | Com (g, f), _ -> evalApp g (evalApp f x)
  | _, Com (x, y) -> com (evalApp f x) (evalApp f y)
  | _, Id x       -> Id (evalApp f x)
  | _, _          -> App (f, x)

and evalProp ctx = function
  | True             -> True
  | False            -> False
  | And (a, b)       -> And (evalProp ctx a, evalProp ctx b)
  | Or (a, b)        -> Or (evalProp ctx a, evalProp ctx b)
  | Impl (a, b)      -> Impl (evalProp ctx a, evalProp ctx b)
  | Eq (t1, t2)      -> Eq (eval ctx t1, eval ctx t2)
  | Forall (x, t, e) -> let t' = eval ctx t in Forall (x, t', evalProp (upVar ctx x t') e)
  | Exists (x, t, e) -> let t' = eval ctx t in Exists (x, t', evalProp (upVar ctx x t') e)

let rec subst ctx x e = function
  | U n           -> U n
  | Var y         -> if x = y then e else Var y
  | Dom g         -> dom ctx (subst ctx x e g)
  | Cod g         -> cod ctx (subst ctx x e g)
  | Id a          -> Id (subst ctx x e a)
  | App (f, a)    -> evalApp (subst ctx x e f) (subst ctx x e a)
  | Com (f, g)    -> com (subst ctx x e f) (subst ctx x e g)
  | Hom (t, a, b) -> Hom (subst ctx x e t, subst ctx x e a, subst ctx x e b)
  | Eps c         -> substClos eps ctx x e c

and substProp ctx x e = function
  | True          -> True
  | False         -> False
  | And (a, b)    -> And  (substProp ctx x e a, substProp ctx x e b)
  | Or (a, b)     -> Or   (substProp ctx x e a, substProp ctx x e b)
  | Impl (a, b)   -> Impl (substProp ctx x e a, substProp ctx x e b)
  | Eq (t1, t2)   -> Eq (subst ctx x e t1, subst ctx x e t2)
  | Forall c      -> substClos forall ctx x e c
  | Exists c      -> substClos exists ctx x e c

and substClos : 't. (clos -> 't) -> term Env.t -> ident -> term -> clos -> 't =
  fun ctor ctx x e (y, t, i) -> if x = y then ctor (y, t, i)
    else ctor (y, subst ctx x e t, substProp ctx x e i)

let rec conv ctx t1 t2 = match t1, t2 with
  | U n,              U m              -> n = m
  | Var x,            Var y            -> x = y
  | Dom f,            Dom g            -> conv ctx f g
  | Cod f,            Cod g            -> conv ctx f g
  | Id x,             Id y             -> conv ctx x y
  | Com (f1, g1),     Com (f2, g2)     -> conv ctx f1 f2 && conv ctx g1 g2
  | App (f1, x1),     App (f2, x2)     -> conv ctx f1 f2 && conv ctx x1 x2
  | Hom (t1, a1, b1), Hom (t2, a2, b2) -> conv ctx t1 t2 && conv ctx a1 a2 && conv ctx b1 b2
  | Eps c1,           Eps c2           -> convClos ctx c1 c2
  | _,                _                -> false

and convProp ctx e1 e2 = match e1, e2 with
  | True,             True             -> true
  | False,            False            -> true
  | And (a1, b1),     And (a2, b2)     -> convProp ctx a1 a2 && convProp ctx b1 b2
  | Or (a1, b1),      Or (a2, b2)      -> convProp ctx a1 a2 && convProp ctx b1 b2
  | Impl (a1, b1),    Impl (a2, b2)    -> convProp ctx a1 a2 && convProp ctx b1 b2
  | Eq (a1, b1),      Eq (a2, b2)      -> conv ctx a1 a2 && conv ctx b1 b2
  | Forall c1,        Forall c2        -> convClos ctx c1 c2
  | Exists c1,        Exists c2        -> convClos ctx c1 c2
  | _,                _                -> false

and convClos ctx (x, t1, i1) (y, t2, i2) = conv ctx t1 t2 &&
  let c = freshTerm "σ" in convProp ctx (substProp ctx x c i1) (substProp ctx y c i2)

let eqNf ctx t1 t2 = if not (conv ctx t1 t2) then raise (Ineq (t1, t2))

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

and checkAp ctx f x =
  match check ctx f, check ctx x with
  | Hom (U _, c1, c2), Hom (c, a, b) -> eqNf ctx c c1; Hom (c2, evalApp f a, evalApp f b)
  | Hom (U _, c1, c2), c             -> eqNf ctx c c1; c2
  | t,                 _             -> raise (ExpectedUniv t)

and checkProp ctx = function
  | True          -> ()
  | False         -> ()
  | And (a, b)    -> checkProp2 ctx a b
  | Or (a, b)     -> checkProp2 ctx a b
  | Impl (a, b)   -> checkProp2 ctx a b
  | Eq (t1, t2)   -> eqNf ctx (check ctx t1) (check ctx t2)
  | Forall c      -> checkClos ctx c
  | Exists c      -> checkClos ctx c

and checkProp2 ctx e1 e2 =
  checkProp ctx e1; checkProp ctx e2

and checkClos ctx (x, t, e) =
  ignore (extUniv (check ctx t)); checkProp (upVar ctx x t) e
