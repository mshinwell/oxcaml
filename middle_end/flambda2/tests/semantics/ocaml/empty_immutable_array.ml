(* The immutable array with no element: the same static constant as the array
   with no element. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external length : 'a iarray -> int = "%array_length"

let none : int iarray = [: :]

let result = length (opaque none) + 7
