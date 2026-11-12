(* A function that takes a function and is always inlined, given an exported
   function that is never inlined: the two calls of the argument stay, as direct
   calls. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline] twice f x = f (f x)

let[@inline never] succ x = x + 1

let add2 x = twice succ x
