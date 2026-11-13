(* A literal with a variable between two constants. gives: s = 24 *)

let[@inline never] [@local never] make (x : int) : int iarray = [: 1; x; 3 :]

let s : int =
  let a = make (Sys.opaque_identity 20) in
  Iarray.get a 0 + Iarray.get a 1 + Iarray.get a 2
