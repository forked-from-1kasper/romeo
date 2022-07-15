open Parser

let perform = function
  | Def (e1, e2) -> Printf.printf "%s & %s\n" (showSExp e1) (showSExp (unpack e2))
  | Eof          -> ()

let checkFile filename =
  let chan  = open_in filename in
  let input = Monad.ofChan chan in

  let eof = ref false in
  let pos = ref 0 in

  while not !eof do
    match Monad.runParser cmd input !pos with
    | Error err   -> Printf.printf "Parse error:\n%s\n" err; eof := true
    | Ok (_, Eof) -> eof := true
    | Ok (n, c)   -> pos := n; perform c
  done;
  close_in chan