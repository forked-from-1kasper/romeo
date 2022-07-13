type ident = string * int64

module Ident = struct
  type t = ident
  let compare (s1, i1) (s2, i2) =
    if s1 = s2 then compare i1 i2 else compare s1 s2
end

let ident s = (s, 0L)

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"

let rec showSubscript x =
  if x < 0L then failwith "showSubscript: expected positive integer"
  else if x = 0L then "" else
    let (y, d) = (Int64.div x 10L, Int64.rem x 10L) in
    showSubscript y ^ getDigit (Int64.to_int d)

module Env = Map.Make(Ident)

let gidx : int64 ref = ref 0L
let gen () = gidx := Int64.succ !gidx; !gidx

let freshName x = let n = gen () in (x ^ showSubscript n, n)
let fresh (p, _) = (p, gen ())