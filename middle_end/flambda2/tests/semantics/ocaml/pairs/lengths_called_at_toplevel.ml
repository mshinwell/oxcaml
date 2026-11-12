(* A toplevel that calls a function of another unit: the load and the call are
   run when the unit is. *)

let three = Lengths.length (Cons (1, Cons (2, Cons (3, Nil))))
