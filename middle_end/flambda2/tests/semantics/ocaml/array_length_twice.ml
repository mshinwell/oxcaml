(* A sum over an array by a recursive function that takes the length of the
   array for its test and reads with a check, which takes the length again.
   Simplify takes the length once. The array given has no element, so nothing is
   read. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external ( = ) : int -> int -> bool = "%equal"

external aget : 'a array -> int -> 'a = "%array_safe_get"

external alength : 'a array -> int = "%array_length"

let rec sum (a : int array) i total =
  if i = alength a then total else sum a (i + 1) (total + aget a i)

let none : int array = [||]

let result = sum (opaque none) 0 100
