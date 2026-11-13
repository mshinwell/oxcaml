(* An immutable array of boxed 64-bit integers. gives: v = 3 | n = 2 *)

let[@inline never] [@local never] make (x : int64) : int64 iarray = [: x; 7L :]

let v : int = Int64.to_int (Iarray.get (make 3L) (Sys.opaque_identity 0))

let n : int = Iarray.length (make 3L)
