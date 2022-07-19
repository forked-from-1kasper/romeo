open Prelude
open Parser
open Check
open Ident
open Term
open Eval

let checkedFiles = ref Set.empty
let ctx = { term = alloc (); rho = alloc (); constant = alloc () }

let ppAlreadyDeclared x = Printf.printf "Variable “%s” is already declared.\n" (Pp.showIdent x)

let upGlobal ctx x t =
  if Env.mem x !(ctx.global) then ppAlreadyDeclared x
  else ctx.global := Env.add x t !(ctx.global)

let elab      stx = Term.salt Env.empty (expandTerm (macroexpand (unpack stx)))
let elabProp  stx = Term.saltProp Env.empty (expandProp (macroexpand (unpack stx)))
let elabProof stx = Term.saltProof Env.empty (expandProof (macroexpand stx))

let elabBinder stx = let (is, es) = splitWhile ((<>) (Atom ":")) stx in
  let e = elab (Node (List.tl es)) in List.map (fun i -> (expandIdent i, e)) is

let elabBinders stxs = List.concat (List.map (elabBinder % expandNode) stxs)

let teleCtx f g =
  List.fold_left (fun ctx (s, t0) ->
    let i = f s in let t = g t0 in ignore (Term.extUniv (check ctx t));
    if Env.mem i ctx.term.local then raise (VariableAlreadyDeclared i)
    else { ctx with term = Term.upLocal ctx.term i t })

let informCheck d = Printf.printf "Checking: %s\n" d; flush_all ()

let rec perform = function
  | Macro (e1, e2)       -> let vbs   = collectVariables Set.empty e1 in
                            let value = macroexpand (unpack e2) in
                            macros := { variables = vbs; pattern = e1; value = value } :: !macros
  | Def (k, e1, e2)      -> let (e, bs) = expandDef [] e1 in
                            informCheck (showSExps (extend e));
                            let vbs     = List.map fst bs in
                            let value   = macroexpand (unpack e2) in
                            let ctx0    = teleCtx ident elab ctx (List.rev bs) in
                            begin match k with
                              | Term -> ignore (check ctx0 (Term.salt Env.empty (expandTerm value)))
                              | Prop -> checkProp ctx0 (Term.saltProp Env.empty (expandProp value))
                            end; macros := { variables = Set.of_list vbs; pattern = e; value = value } :: !macros
  | Constants (is, e)    -> let t = elab e in ignore (Term.extUniv (check ctx t)); List.iter (fun i -> informCheck i; upGlobal ctx.term (ident i) t) is
  | Constant (i, es, t0) -> let t    = elab t0 in
                            let bs   = elabBinders es in
                            let ctx0 = teleCtx idfun idfun ctx bs in
                            ignore (Term.extUniv (check ctx0 t));
                            upGlobal ctx.constant (ident i) (bs, t)
  | Macroexpand e        -> Printf.printf "MACROEXPAND: %s\n" (showSExp (macroexpand (unpack e))); flush_all ()
  | Infer e              -> Printf.printf "INFER: %s\n" (Pp.showTerm (check ctx (elab e))); flush_all ()
  | Eval e               -> let t = elab e in ignore (check ctx t); Printf.printf "EVAL: %s\n" (Pp.showTerm (eval ctx t)); flush_all ()
  | Theorem (i, e0, p0)  -> informCheck i; let e = elabProp e0 in let p = elabProof p0 in checkProp ctx e; ensure ctx p e; upGlobal ctx.rho (ident i) e
  | Axiom (i, e0)        -> informCheck i; let e = elabProp e0 in checkProp ctx e; upGlobal ctx.rho (ident i) e
  | Infix (assoc, n, is) -> List.iter (fun i -> operators := Dict.add i (n, assoc) !operators) is
  | Variables is         -> List.iter (fun i -> variables := Set.add i !variables) is
  | Import fs            -> List.iter checkFile fs
  | Comment _            -> ()
  | Eof                  -> ()

and checkFile filename =
  if Set.mem filename !checkedFiles then () else
  begin
    Printf.printf "Checking “%s”.\n" filename;
    let chan  = open_in filename in
    let input = Monad.ofChan chan in

    let eof = ref false in let pos = ref 0 in

    while not !eof do
      match Monad.runParser cmd input !pos with
      | Error err   -> Printf.printf "Parse error:\n%s\n" err; eof := true
      | Ok (_, Eof) -> eof := true
      | Ok (n, c)   -> pos := n; (try perform c with err -> print_endline (Pp.showError err))
    done; close_in chan; checkedFiles := Set.add filename !checkedFiles;
    Printf.printf "File “%s” checked.\n" filename; flush_all ()
  end