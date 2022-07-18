open Term

type environment =
  { term : term context;
    rho  : prop context }

let rec infer ctx = function
  | U n           -> U (Succ n)
  | Var x         -> lookup ctx.term x
  | Dom g | Cod g -> let (t, _, _) = extHom (infer ctx g) in t
  | Id x          -> Hom (infer ctx x, x, x)
  | Com (g, f)    -> let (t, _, c) = extHom (infer ctx g) in
                     let (_, a, _) = extHom (infer ctx f) in
                     Hom (t, a, c)
  | App (f, x)    -> inferAp ctx f x
  | Hom (t, _, _) -> U (extUniv (infer ctx t))
  | Eps x         -> let (_, t, _) = extExUniq (lookup ctx.rho x) in t

and inferAp ctx f x =
  let (_, c1, c2) = extHom (infer ctx f) in match infer ctx x with
  | Hom (c, a, b) when conv ctx c c1 -> Hom (c2, evalApp ctx f a, evalApp ctx f b)
  | _                                -> c2

and eval ctx = function
  | U n           -> U n
  | Var x         -> Var x
  | Dom g         -> dom ctx g
  | Cod g         -> cod ctx g
  | Id x          -> Id (eval ctx x)
  | Com (f, g)    -> com (eval ctx f) (eval ctx g)
  | App (f, x)    -> evalApp ctx (eval ctx f) (eval ctx x)
  | Hom (t, a, b) -> Hom (eval ctx t, eval ctx a, eval ctx b)
  | Eps x         -> Eps x

and dom ctx g = let (_, t, _) = extHom (infer ctx g) in t
and cod ctx g = let (_, _, t) = extHom (infer ctx g) in t

and com f g = match f, g with
  | Com (g, h), f -> com g (com h f)
  | Id _, f       -> f
  | f, Id _       -> f
  | f, g          -> Com (f, g)

and evalApp ctx f x = let (_, c1, _) = extHom (infer ctx f) in match f, x, infer ctx x with
  | Com (g, f), _,          _                                  -> evalApp ctx g (evalApp ctx f x)
  | _,          Com (x, y), Hom (c2, _, _) when conv ctx c1 c2 -> com (evalApp ctx f x) (evalApp ctx f y)
  | _,          Id x,       Hom (c2, _, _) when conv ctx c1 c2 -> Id (evalApp ctx f x)
  | _,          _,          _                                  -> App (f, x)

and evalProp ctx = function
  | True        -> True
  | False       -> False
  | And (a, b)  -> And (evalProp ctx a, evalProp ctx b)
  | Or (a, b)   -> Or (evalProp ctx a, evalProp ctx b)
  | Impl (a, b) -> Impl (evalProp ctx a, evalProp ctx b)
  | Eq (t1, t2) -> Eq (eval ctx t1, eval ctx t2)
  | Forall c    -> evalBinder forall ctx c
  | Exists c    -> evalBinder exists ctx c
  | ExUniq c    -> evalBinder exuniq ctx c

and evalBinder c ctx (x, t, e) = let t' = eval ctx t in
  c (x, t', evalProp { ctx with term = upLocal ctx.term x t' } e)

and subst ctx x e = function
  | U n           -> U n
  | Var y         -> if x = y then e else Var y
  | Dom g         -> dom ctx (subst ctx x e g)
  | Cod g         -> cod ctx (subst ctx x e g)
  | Id a          -> Id (subst ctx x e a)
  | App (f, a)    -> evalApp ctx (subst ctx x e f) (subst ctx x e a)
  | Com (f, g)    -> com (subst ctx x e f) (subst ctx x e g)
  | Hom (t, a, b) -> Hom (subst ctx x e t, subst ctx x e a, subst ctx x e b)
  | Eps x         -> Eps x

and substProp ctx x e = function
  | True          -> True
  | False         -> False
  | And (a, b)    -> And  (substProp ctx x e a, substProp ctx x e b)
  | Or (a, b)     -> Or   (substProp ctx x e a, substProp ctx x e b)
  | Impl (a, b)   -> Impl (substProp ctx x e a, substProp ctx x e b)
  | Eq (t1, t2)   -> Eq (subst ctx x e t1, subst ctx x e t2)
  | Forall c      -> substClos forall ctx x e c
  | Exists c      -> substClos exists ctx x e c
  | ExUniq c      -> substClos exuniq ctx x e c

and substClos ctor ctx x e (y, t, i) =
  if x = y then ctor (y, t, i) else ctor (y, subst ctx x e t, substProp ctx x e i)

and conv ctx t1 t2 = match t1, t2 with
  | U n,              U m              -> n = m
  | Var x,            Var y            -> x = y
  | Dom f,            Dom g            -> conv ctx f g
  | Cod f,            Cod g            -> conv ctx f g
  | Id x,             Id y             -> conv ctx x y
  | Com (f1, g1),     Com (f2, g2)     -> conv ctx f1 f2 && conv ctx g1 g2
  | App (f1, x1),     App (f2, x2)     -> conv ctx f1 f2 && conv ctx x1 x2
  | Hom (t1, a1, b1), Hom (t2, a2, b2) -> conv ctx t1 t2 && conv ctx a1 a2 && conv ctx b1 b2
  | Eps x,            Eps y            -> x = y
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
  | ExUniq c1,        ExUniq c2        -> convClos ctx c1 c2
  | _,                _                -> false

and convClos ctx (x, t1, i1) (y, t2, i2) = conv ctx t1 t2 &&
  let c = freshTerm "σ" in convProp ctx (substProp ctx x c i1) (substProp ctx y c i2)

let eqNf ctx t1 t2 = if not (conv ctx t1 t2) then raise (Ineq (t1, t2))