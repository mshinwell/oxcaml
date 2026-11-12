(* Comparisons are of signed numbers, at each width. *)

external ( < ) : int -> int -> bool = "%lessthan"

external lt32 : int32 -> int32 -> bool = "%lessthan"

external lt64 : int64 -> int64 -> bool = "%lessthan"

let minus_one_below_zero = -1 < 0

let least_below_largest = -4611686018427387904 < 4611686018427387903

let least_below_largest_32 = lt32 (-2147483648l) 2147483647l

let minus_one_below_zero_64 = lt64 (-1L) 0L

let largest_below_least_64 = lt64 9223372036854775807L (-9223372036854775808L)
