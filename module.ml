open Parser
open Check
open Ident
open Term
open Eval

let checkedFiles = ref Set.empty
let ctx = ref { term = Env.empty; proof = Env.empty }

let ppAlreadyDeclared x = Printf.printf "Variable “%s” is already declared.\n" (Pp.showIdent x)

let upGlobal x t =
  if Env.mem x !ctx.term then ppAlreadyDeclared x
  else ctx := { term = Term.upVar !ctx.term x t; proof = !ctx.proof }

let upThm x t =
  if Env.mem x !ctx.proof then ppAlreadyDeclared x
  else ctx := { term = !ctx.term; proof = Env.add x t !ctx.proof }

let elab      stx = Term.salt Env.empty (expandTerm (macroexpand (unpack stx)))
let elabProp  stx = Term.saltProp Env.empty (expandProp (macroexpand (unpack stx)))
let elabProof stx = Term.saltProof Env.empty (expandProof (macroexpand stx))

let rec perform = function
  | Macro (e1, e2)       -> let vbs   = collectVariables Set.empty e1 in
                            let value = macroexpand (unpack e2) in
                            macros := { variables = vbs; pattern = e1; value = value } :: !macros
  | Def (e1, e2)         -> let (e, bs) = expandDef [] e1 in
                            let vbs     = List.map fst bs in
                            let value   = macroexpand (unpack e2) in
                            let ctx0    = List.fold_left (fun ctx (s, t0) ->
                              let i = ident s in let t = elab t0 in ignore (Term.extUniv (check ctx t));
                              if Env.mem i ctx then raise (VariableAlreadyDeclared i)
                              else Term.upVar ctx i t) !ctx.term (List.rev bs) in
                            ignore (check ctx0 (Term.salt Env.empty (expandTerm value)));
                            macros := { variables = Set.of_list vbs; pattern = e; value = value } :: !macros
  | Postulate (is, e)    -> let t = elab e in ignore (Term.extUniv (check !ctx.term t)); List.iter (fun i -> upGlobal (ident i) t) is
  | Infer e              -> print_endline (Pp.showTerm (check !ctx.term (elab e)))
  | Eval e               -> let t = elab e in ignore (check !ctx.term t); print_endline (Pp.showTerm (eval !ctx.term t))
  | Theorem (i, e0, p0)  -> let e = elabProp e0 in let p = elabProof p0 in checkProp !ctx.term e; ensure !ctx p e; upThm (ident i) e
  | Axiom (i, e0)        -> let e = elabProp e0 in checkProp !ctx.term e; upThm (ident i) e
  | Infix (assoc, n, is) -> List.iter (fun i -> operators := Dict.add i (n, assoc) !operators) is
  | Variables is         -> List.iter (fun i -> variables := Set.add i !variables) is
  | Import fs            -> List.iter checkFile fs
  | Comment _            -> ()
  | Eof                  -> ()

and checkFile filename =
  if Set.mem filename !checkedFiles then () else

  let chan  = open_in filename in
  let input = Monad.ofChan chan in

  let eof = ref false in
  let pos = ref 0 in

  while not !eof do
    match Monad.runParser cmd input !pos with
    | Error err   -> Printf.printf "Parse error:\n%s\n" err; eof := true
    | Ok (_, Eof) -> eof := true
    | Ok (n, c)   -> pos := n; (try perform c with err -> print_endline (Pp.showError err))
  done; close_in chan; checkedFiles := Set.add filename !checkedFiles;
  Printf.printf "File “%s” checked.\n" filename