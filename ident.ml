type ident = string * int64

module Ident = struct
  type t = ident
  let compare (s1, i1) (s2, i2) =
    if s1 = s2 then compare i1 i2 else compare s1 s2
end

let getDigit x = Char.chr (Z.to_int x + 0x80) |> Printf.sprintf "\xE2\x82%c"
let ten = Z.of_int 10

let rec showSubscript x =
  if Z.lt x Z.zero then failwith "showSubscript: expected positive integer"
  else if Z.equal x Z.zero then "" else let (y, d) = Z.div_rem x ten in
    showSubscript y ^ getDigit d

module Env = Map.Make(Ident)

let gidx : int64 ref = ref 0L
let gen () = gidx := Int64.succ !gidx; !gidx

let freshName x = let n = gen () in
  (x ^ showSubscript (Z.of_int64 n), n)

let fresh (p, _) = (p, gen ())