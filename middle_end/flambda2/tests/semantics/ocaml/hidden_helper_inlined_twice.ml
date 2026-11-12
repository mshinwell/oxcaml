(* A module whose signature hides a helper that two of its functions call. The
   two functions are never inlined: each of their closures holds the helper in a
   value slot. Simplify inlines the helper in the code of both and removes the
   two slots, the closure of the helper and its code. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

module Squares : sig
  val sum : int -> int -> int

  val difference : int -> int -> int
end = struct
  let square x = x * x

  let[@inline never] sum a b = square a + square b

  let[@inline never] difference a b = square a - square b
end

let result = Squares.sum (opaque 3) 4 + Squares.difference 5 (opaque 2)
