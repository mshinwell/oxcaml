(* A test in a branch of a test, with calls in two of the three branches and a
   constant in the third, and nothing using what it gives. Simplify removes the
   parameter of the continuation after the outer test, and each of the two calls
   returns to a new continuation that takes the result and applies the old one
   to nothing. The functions are exported, so that they stay functions. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] twice (x : int) : int = x + x

let[@inline never] ignored (c : bool) (d : bool) (x : int) : int =
  let _ = if c then if d then twice x else 8 else twice (x + 1) in
  x + 1

let result = ignored (opaque true) (opaque true) 3
