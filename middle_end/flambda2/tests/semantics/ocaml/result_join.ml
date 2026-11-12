(* A variant with two constructors that hold a field, built on both paths and
   matched after they meet. Simplify gives the continuation where they meet the
   tag and the field of each constructor in place of the block, with [poison]
   for the field of the constructor that a path has not made, and no block is
   made. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

type outcome =
  | Done of int
  | Failed of int

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then Done (x + 1) else Failed x in
  match v with Done y -> y + 2 | Failed e -> 0 - e

let result = f true 3 + f false 4
