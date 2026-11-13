(* A function that is kept returns the immutable array of its two parameters;
   both are read. gives: p = 3 | q = 4 *)

let[@inline never] [@local never] make (x : int) (y : int) : int iarray =
  [: x; y :]

let a : int iarray = make 3 (Sys.opaque_identity 4)

let p : int = Iarray.get a 0

let q : int = Iarray.get a 1
