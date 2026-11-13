(* The unit exports an immutable array made as it runs: a field of the block of
   the module. gives: table = [4; 5; 6] | n = 3 *)

let[@inline never] [@local never] make (x : int) : int iarray =
  [: x; x + 1; x + 2 :]

let table : int iarray = make (Sys.opaque_identity 4)

let n : int = Iarray.length table
