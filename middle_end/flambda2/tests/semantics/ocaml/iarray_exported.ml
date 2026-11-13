(* The unit exports an immutable array, one of whose elements is not a
   constant. Simplify makes the array a symbol bound to a static array and
   the load from it the element. The validation reads the element and lifts
   the array: the two runs return the same, and the unit is validated. *)

external opaque : 'a -> 'a = "%opaque"

external get : 'a iarray -> int -> 'a = "%array_unsafe_get"

let weights = [: 5; opaque 3; 8 :]

let result = get weights 1
