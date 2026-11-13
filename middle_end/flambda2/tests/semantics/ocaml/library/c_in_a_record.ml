(* A record with a field that is an immutable array, made by one function and
   read by another. gives: w = 211 *)

type shelf =
  { id : int;
    items : int iarray
  }

let[@inline never] [@local never] make (id : int) (x : int) : shelf =
  { id; items = [: x; x + 1 :] }

let[@inline never] [@local never] weight (s : shelf) =
  (s.id * 100) + Iarray.get s.items 0 + Iarray.get s.items 1

let w : int = weight (make 2 (Sys.opaque_identity 5))
