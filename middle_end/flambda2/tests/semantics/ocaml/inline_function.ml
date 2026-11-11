(* Two small functions, called directly. Simplify inlines both calls of [square]
   and the call of [add_squares], and nothing is left of the functions. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let square x = x * x

let add_squares a b = square a + square b

let result = add_squares (opaque 3) 4
