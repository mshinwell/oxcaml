(* A test of whether an array is empty, by its length, in a function that is
   given the array with no element. *)

external opaque : 'a -> 'a = "%opaque"

external ( = ) : int -> int -> bool = "%equal"

external alength : 'a array -> int = "%array_length"

let is_empty (a : int array) = alength a = 0

let none : int array = [||]

let result = if is_empty (opaque none) then 1 else 2
