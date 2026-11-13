(* An immutable array of two closures over the parameter; one is read and
   applied. gives: add = 8 | mul = 15 *)

let[@inline never] [@local never] ops (k : int) : (int -> int) iarray =
  [: (fun n -> n + k); (fun n -> n * k) :]

let add : int = (Iarray.get (ops 3) 0) 5

let mul : int = (Iarray.get (ops (Sys.opaque_identity 3)) 1) 5
