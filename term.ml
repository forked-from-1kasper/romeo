open Ident

type term =
  | U      of Z.t
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

let freshVar x = Var (freshName x)

type ctx = term Env.t

exception VariableNotFound of ident
exception ExpectedUniv     of term
exception ExpectedHom      of term

let extUniv = function
  | U n -> n
  | t   -> raise (ExpectedUniv t)

let lookup ctx x =
  match Env.find_opt x ctx with
  | None   -> raise (VariableNotFound x)
  | Some t -> t

let rec infer ctx = function
  | U n           -> U (Z.succ n)
  | Var x         -> lookup ctx x
  | Dom g | Cod g -> let (t, _, _) = extHom ctx g in t
  | Id x          -> Hom (infer ctx x, x, x)
  | Com (g, f)    -> let (t, _, c) = extHom ctx g in let (_, a, _) = extHom ctx f in Hom (t, a, c)
  | App (f, x)    -> inferAp ctx f x
  | Hom (t, _, _) -> U (extUniv (infer ctx t))
  | Eps (_, t, _) -> t

and extHom ctx g =
  match infer ctx g with
  | Hom (t, a, b) -> (t, a, b)
  | t             -> raise (ExpectedHom t)

and inferAp ctx f x =
  let (_, _, c) = extHom ctx f in match infer ctx x with
  | Hom (_, a, b) -> Hom (c, App (f, a), App (f, b))
  | _             -> c

let rec eval ctx = function
  | U n           -> U n
  | Var x         -> Var x
  | Dom g         -> let (_, t, _) = extHom ctx g in t
  | Cod g         -> let (_, _, t) = extHom ctx g in t
  | Id x          -> Id (eval ctx x)
  | Com (f, g)    -> com (eval ctx f) (eval ctx g)
  | App (f, x)    -> app f x
  | Hom (t, a, b) -> Hom (eval ctx t, eval ctx a, eval ctx b)
  | Eps (x, t, e) -> Eps (x, eval ctx t, e)

and com f g = match f, g with
  | Com (g, h), f -> com g (com h f)
  | Id _, f       -> f
  | f, Id _       -> f
  | f, g          -> Com (f, g)

and app f = function
  | Com (x, y) -> com (app f x) (app f y)
  | Id x       -> Id (app f x)
  | x          -> App (f, x)

let rec subst x e = function
  | U n           -> U n
  | Var y         -> if x = y then e else Var y
  | Dom g         -> Dom (subst x e g)
  | Cod g         -> Cod (subst x e g)
  | Id a          -> Id (subst x e a)
  | App (f, a)    -> App (subst x e f, subst x e a)
  | Com (f, g)    -> Com (subst x e f, subst x e g)
  | Hom (t, a, b) -> Hom (subst x e t, subst x e a, subst x e b)
  | Eps c         -> substClos eps x e c

and substProp x e = function
  | True          -> True
  | False         -> False
  | And (a, b)    -> And (substProp x e a, substProp x e b)
  | Or (a, b)     -> Or (substProp x e a, substProp x e b)
  | Impl (a, b)   -> Impl (substProp x e a, substProp x e b)
  | Eq (t1, t2)   -> Eq (subst x e t1, subst x e t2)
  | Forall c      -> substClos forall x e c
  | Exists c      -> substClos exists x e c

and substClos : 't. (clos -> 't) -> ident -> term -> clos -> 't =
  fun ctor x e (y, t, i) -> if x = y then ctor (y, t, i)
    else ctor (y, subst x e t, substProp x e i)

let rec conv t1 t2 = match t1, t2 with
  | U n,              U m              -> Z.equal n m
  | Var x,            Var y            -> x = y
  | Dom f,            Dom g            -> conv f g
  | Cod f,            Cod g            -> conv f g
  | Id x,             Id y             -> conv x y
  | Com (f1, g1),     Com (f2, g2)     -> conv f1 f2 && conv g1 g2
  | App (f1, x1),     App (f2, x2)     -> conv f1 f2 && conv x1 x2
  | Hom (t1, a1, b1), Hom (t2, a2, b2) -> conv t1 t2 && conv a1 a2 && conv b1 b2
  | Eps c1,           Eps c2           -> convClos c1 c2
  | _,                _                -> t1 = t2

and convProp e1 e2 = match e1, e2 with
  | True,             True             -> true
  | False,            False            -> true
  | And (a1, b1),     And (a2, b2)     -> convProp a1 a2 && convProp b1 b2
  | Or (a1, b1),      Or (a2, b2)      -> convProp a1 a2 && convProp b1 b2
  | Impl (a1, b1),    Impl (a2, b2)    -> convProp a1 a2 && convProp b1 b2
  | Eq (a1, b1),      Eq (a2, b2)      -> conv a1 a2 && conv b1 b2
  | Forall c1,        Forall c2        -> convClos c1 c2
  | Exists c1,        Exists c2        -> convClos c1 c2
  | _,                _                -> false

and convClos (x, t1, i1) (y, t2, i2) = conv t1 t2 &&
  let c = freshVar "σ" in convProp (substProp x c i1) (substProp y c i2)