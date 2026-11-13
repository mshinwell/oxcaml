(* An array made by a function that is kept, read at two constant indices.
   gives: a = 10 | b = 12 *)

let[@inline never] [@local never] make (x : int) : int iarray =
  [: x; x + 1; x + 2 :]

let a : int = Iarray.get (make 10) 0

let b : int = Iarray.get (make (Sys.opaque_identity 10)) 2
