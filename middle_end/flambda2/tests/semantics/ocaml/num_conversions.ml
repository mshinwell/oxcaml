(* Conversions between the integers of different widths, of numbers that
   Simplify does not know. *)

external ( + ) : int -> int -> int = "%addint"

external int64_of_int32 : int32 -> int64 = "%int64_of_int32"

external nativeint_of_int : int -> nativeint = "%nativeint_of_int"

external int_of_int64 : int64 -> int = "%int64_to_int"

external int_of_nativeint : nativeint -> int = "%nativeint_to_int"

external int_of_int32 : int32 -> int = "%int32_to_int"

external opaque : 'a -> 'a = "%opaque"

let result =
  int_of_int64 (int64_of_int32 (opaque 5l))
  + int_of_nativeint (nativeint_of_int (opaque 6))
  + int_of_int32 (opaque 7l)
