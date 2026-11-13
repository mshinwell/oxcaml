(* The arms make arrays of one and of three elements; the last element is read
   by the length. gives: one = 4 | three = 6 *)

let[@inline never] [@local never] last (c : bool) (x : int) (y : int) (z : int)
    =
  let a : int iarray = if c then [: x :] else [: x; y; z :] in
  Iarray.get a (Iarray.length a - 1)

let one : int = last true 4 5 6

let three : int = last (Sys.opaque_identity false) 4 5 6
