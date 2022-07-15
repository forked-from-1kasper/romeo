open Parser
open Ident

let ctx = ref Env.empty

let upGlobal x t = ctx := Term.upVar !ctx x t

let elab stx = Term.salt Env.empty (expandTerm (unpack stx))

let perform = function
  | Def (e1, e2)      -> Printf.printf "%s & %s\n" (showSExp e1) (showSExp (unpack e2))
  | Postulate (is, e) -> let t = elab e in ignore (Term.extUniv (Term.check !ctx t)); List.iter (fun i -> upGlobal (ident i) t) is
  | Infer e           -> print_endline (Pp.showTerm (Term.check !ctx (elab e)))
  | Eval e            -> let t = elab e in ignore (Term.check !ctx t); print_endline (Pp.showTerm (Term.eval !ctx t))
  | Comment _         -> ()
  | Eof               -> ()

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