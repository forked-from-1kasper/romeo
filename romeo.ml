open Deriv
open Ident
open Term
open Pp

type cmdline =
  | Help

let banner = "Castle Romeo theorem prover, version 0.0.0"
let help =
"   invoke = romeo | romeo list
     list = [] | command list
  command = help"

let defaults : cmdline list -> cmdline list = function
  | [] -> [Help]
  | xs -> xs

let rec parseArgs : string list -> cmdline list = function
  | "help" :: rest -> Help :: parseArgs rest
  | x :: xs -> Printf.printf "Unknown command “%s”\n" x; parseArgs xs
  | [] -> []

let cmd : cmdline -> unit = function
  | Help -> print_endline banner; print_endline help

let () = Array.to_list Sys.argv
         |> List.tl  |> parseArgs
         |> defaults |> List.iter cmd