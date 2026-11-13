(* One arm of a test gives the empty array and the other an array of two
   elements. gives: zero = 0 | two = 2 *)

let[@inline never] [@local never] run (c : bool) (x : int) =
  let a : int iarray = if c then [: :] else [: x; x :] in
  Iarray.length a

let zero : int = run (Sys.opaque_identity true) 3

let two : int = run false 3
