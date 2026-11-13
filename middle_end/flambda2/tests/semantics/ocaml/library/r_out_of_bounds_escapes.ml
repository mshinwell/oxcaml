(* A read past the end with no handler: the unit ends with the exception. gives:
   the exception Invalid_argument "index out of bounds" *)

let[@inline never] [@local never] make (x : int) : int iarray = [: x; x + 1 :]

let inside : int = Iarray.get (make 5) 1

let outside : int = Iarray.get (make 5) (Sys.opaque_identity 7)
