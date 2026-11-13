(* The unit exports an immutable array, one of whose elements is not a
   constant. Simplify makes the array a symbol bound to a static array,
   which the validation does not follow: the two runs return the same
   elements, and the unit is not validated. *)

external opaque : 'a -> 'a = "%opaque"

external get : 'a iarray -> int -> 'a = "%array_unsafe_get"

let weights = [: 5; opaque 3; 8 :]

let result = get weights 1
