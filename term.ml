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
  | ExUniq of clos

and clos = ident * term * prop

let eps    (x, t, i) = Eps    (x, t, i)
let forall (x, t, i) = Forall (x, t, i)
let exists (x, t, i) = Exists (x, t, i)
let exuniq (x, t, i) = ExUniq (x, t, i)
let app f x          = App    (f, x)

let freshTerm x = Var (freshName x)

exception VariableNotFound of ident
exception ExpectedUniv     of term
exception ExpectedHom      of term
exception Ineq             of term * term

exception IneqProp       of prop * prop
exception ExpectedAnd    of prop
exception ExpectedImpl   of prop
exception ExpectedForall of prop
exception ExpectedExists of prop
exception ExpectedEq     of prop

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
  | Eps (x, t, e)    -> let y = fresh x in Eps (y, salt ns t, saltProp (Env.add x y ns) e)

and saltProp ns = function
  | True             -> True
  | False            -> False
  | And (a, b)       -> And (saltProp ns a, saltProp ns b)
  | Or (a, b)        -> Or (saltProp ns a, saltProp ns b)
  | Impl (a, b)      -> Impl (saltProp ns a, saltProp ns b)
  | Eq (t1, t2)      -> Eq (salt ns t1, salt ns t2)
  | Forall (x, t, e) -> let y = fresh x in Forall (y, salt ns t, saltProp (Env.add x y ns) e)
  | Exists (x, t, e) -> let y = fresh x in Exists (y, salt ns t, saltProp (Env.add x y ns) e)
  | ExUniq (x, t, e) -> let y = fresh x in Exists (y, salt ns t, saltProp (Env.add x y ns) e)
