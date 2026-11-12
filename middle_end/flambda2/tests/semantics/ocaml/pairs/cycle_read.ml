(* A toplevel that reads a block of another unit which is part of a cycle, and a
   field of that block. *)

let head = match Cycle.ones with Cons (x, _) -> x | Nil -> 0
