(* A checked read of the array with no element. The check fails and raises
   [Invalid_argument], which the handler catches by name: it compares what was
   raised with that exception. *)

external opaque : 'a -> 'a = "%opaque"

external aget : 'a array -> int -> 'a = "%array_safe_get"

let none : int array = [||]

let result = try aget (opaque none) 0 with Invalid_argument _ -> 7
