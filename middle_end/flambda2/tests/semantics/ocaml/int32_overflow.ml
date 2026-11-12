(* Arithmetic on 32-bit integers wraps round at 32 bits. *)

external add : int32 -> int32 -> int32 = "%int32_add"

external mul : int32 -> int32 -> int32 = "%int32_mul"

external sub : int32 -> int32 -> int32 = "%int32_sub"

external to_int : int32 -> int = "%int32_to_int"

let above_the_largest = to_int (add 2147483647l 1l)

let below_the_least = to_int (sub (-2147483648l) 1l)

let two_to_the_32 = to_int (mul 65536l 65536l)

let the_largest_squared = to_int (mul 2147483647l 2147483647l)
