open Ident
open Term

(* https://github.com/ocaml/ocaml/blob/b8dbb53531806b3ecf8e0a21e9c481d2d17779ad/stdlib/list.ml#L575-L579 *)
let rec convList fn l1 l2 =
  match l1, l2 with
  |    [],       []    -> true
  |    [],     _ :: _  -> false
  | _  :: _,     []    -> false
  | a1 :: l1, a2 :: l2 -> fn a1 a2 && convList fn l1 l2

type tele = (ident * term) list * term

type environment =
  { term     : term context;
    constant : tele context;
    rho      : prop context }

let rec infer ctx = function
  | U n           -> U (Succ n)
  | Var x         -> lookup ctx.term x
  | Const (x, es) -> let (ts, t) = lookup ctx.constant x in
                     let rho = List.map2 (fun (i, _) e -> (i, e)) ts es in
                     subst ctx (Env.of_seq (List.to_seq rho)) t
  | Dom g | Cod g -> let (t, _, _) = extHom (infer ctx g) in t
  | Id x          -> Hom (infer ctx x, x, x)
  | Com (g, f)    -> let (t, _, c) = extHom (infer ctx g) in
                     let (_, a, _) = extHom (infer ctx f) in
                     Hom (t, a, c)
  | App (f, x)    -> inferAp ctx f x
  | Hom (t, _, _) -> U (extUniv (infer ctx t))
  | Eps x         -> let (_, t, _) = extExists (lookup ctx.rho x) in t

and inferAp ctx f x =
  let (_, c1, c2) = extHom (infer ctx f) in match infer ctx x with
  | Hom (c, a, b) when conv ctx c c1 -> Hom (c2, evalApp ctx f a, evalApp ctx f b)
  | _                                -> c2

and eval ctx = function
  | U n           -> U n
  | Var x         -> Var x
  | Const (x, ts) -> Const (x, List.map (eval ctx) ts)
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

and subst ctx rho = function
  | U n                      -> U n
  | Var x when Env.mem x rho -> Env.find x rho
  | Var y                    -> Var y
  | Const (y, ts)            -> Const (y, List.map (subst ctx rho) ts)
  | Dom g                    -> dom ctx (subst ctx rho g)
  | Cod g                    -> cod ctx (subst ctx rho g)
  | Id a                     -> Id (subst ctx rho a)
  | App (f, a)               -> evalApp ctx (subst ctx rho f) (subst ctx rho a)
  | Com (f, g)               -> com (subst ctx rho f) (subst ctx rho g)
  | Hom (t, a, b)            -> Hom (subst ctx rho t, subst ctx rho a, subst ctx rho b)
  | Eps x                    -> Eps x

and substProp ctx rho = function
  | True          -> True
  | False         -> False
  | And (a, b)    -> And  (substProp ctx rho a, substProp ctx rho b)
  | Or (a, b)     -> Or   (substProp ctx rho a, substProp ctx rho b)
  | Impl (a, b)   -> Impl (substProp ctx rho a, substProp ctx rho b)
  | Eq (t1, t2)   -> Eq (subst ctx rho t1, subst ctx rho t2)
  | Forall c      -> substClos forall ctx rho c
  | Exists c      -> substClos exists ctx rho c
  | ExUniq c      -> substClos exuniq ctx rho c

and substClos ctor ctx rho (x, t, i) =
  if Env.mem x rho then ctor (x, t, i)
  else ctor (x, subst ctx rho t, substProp ctx rho i)

and subst1     ctx x e = subst     ctx (Env.add x e Env.empty)
and substProp1 ctx x e = substProp ctx (Env.add x e Env.empty)

and conv ctx t1 t2 = match t1, t2 with
  | U n,              U m              -> n = m
  | Var x,            Var y            -> x = y
  | Const (x, ts1),   Const (y, ts2)   -> x = y && convList (conv ctx) ts1 ts2
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
  let c = freshTerm "σ" in convProp ctx (substProp1 ctx x c i1) (substProp1 ctx y c i2)

let eqNf ctx t1 t2 = if not (conv ctx t1 t2) then raise (Ineq (t1, t2))