open Parser
open Check
open Ident
open Eval

let ctx = ref { term = Env.empty; proof = Env.empty }

let ppAlreadyDeclared x = Printf.printf "Variable “%s” is already declared.\n" (Pp.showIdent x)

let upGlobal x t =
  if Env.mem x !ctx.term then ppAlreadyDeclared x
  else ctx := { term = Term.upVar !ctx.term x t; proof = !ctx.proof }

let upThm x t =
  if Env.mem x !ctx.proof then ppAlreadyDeclared x
  else ctx := { term = !ctx.term; proof = Env.add x t !ctx.proof }

let elab      stx = Term.salt Env.empty (expandTerm (unpack stx))
let elabProp  stx = Term.saltProp Env.empty (expandProp (unpack stx))
let elabProof stx = saltProof Env.empty (expandProof (unpack stx))

let perform = function
  | Def (e1, e2)        -> Printf.printf "%s & %s\n" (showSExp e1) (showSExp (unpack e2))
  | Postulate (is, e)   -> let t = elab e in ignore (Term.extUniv (check !ctx.term t)); List.iter (fun i -> upGlobal (ident i) t) is
  | Infer e             -> print_endline (Pp.showTerm (check !ctx.term (elab e)))
  | Eval e              -> let t = elab e in ignore (check !ctx.term t); print_endline (Pp.showTerm (eval !ctx.term t))
  | Theorem (i, e0, p0) -> let e = elabProp e0 in let p = elabProof p0 in checkProp !ctx.term e; ensure !ctx p e; upThm (ident i) e
  | Axiom (i, e0)       -> let e = elabProp e0 in checkProp !ctx.term e; upThm (ident i) e
  | Comment _           -> ()
  | Eof                 -> ()

let checkFile filename =
  let chan  = open_in filename in
  let input = Monad.ofChan chan in

  let eof = ref false in
  let pos = ref 0 in

  while not !eof do
    match Monad.runParser cmd input !pos with
    | Error err   -> Printf.printf "Parse error:\n%s\n" err; eof := true
    | Ok (_, Eof) -> eof := true
    | Ok (n, c)   -> pos := n; (try perform c with err -> print_endline (Pp.showError err))
  done;
  close_in chan