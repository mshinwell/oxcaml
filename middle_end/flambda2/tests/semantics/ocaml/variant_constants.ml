(* A variant that each path gives as a constant block of another constructor,
   both symbols of the unit, matched after they meet, in a function that is not
   inlined. Simplify gives the continuation where they meet the tag and the
   fields of both constructors: those of the block on each path, and [poison]
   for those of the other constructor. *)

external ( + ) : int -> int -> int = "%addint"

type t =
  | One of int
  | Two of int * int

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then One 1 else Two (2, 3) in
  match v with One y -> x + y | Two (y, z) -> x + y + z

let result = f true 3 + f false 4
