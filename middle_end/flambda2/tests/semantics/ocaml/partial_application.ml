(* A function of two arguments applied to one, and the result to another.
   Simplify makes the second call a direct call of [add] and inlines it. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let add a b = a + b

let result =
  let add_one = add 1 in
  add_one (opaque 2)
