(* The length of an array with no element. The front end makes of [[||]] the
   static constant [Empty_array]; nothing is read or written. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : 'a array -> int = "%array_length"

let none : int array = [||]

let result = length (opaque none) + 5
