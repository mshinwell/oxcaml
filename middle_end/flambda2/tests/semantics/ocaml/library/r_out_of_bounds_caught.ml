(* A read past the end of an array made as the unit runs; the handler catches
   any exception. gives: inside = 6 | outside = -1 *)

let[@inline never] [@local never] read (a : int iarray) (i : int) =
  try Iarray.get a i with _ -> -1

let[@inline never] [@local never] make (x : int) : int iarray = [: x; x + 1 :]

let inside : int = read (make 5) 1

let outside : int = read (make 5) (Sys.opaque_identity 2)
