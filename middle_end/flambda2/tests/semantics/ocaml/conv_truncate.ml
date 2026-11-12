(* Conversions to a narrower integer keep the low bits and extend the sign. *)

external int32_of_int64 : int64 -> int32 = "%int64_to_int32"

external int32_of_int : int -> int32 = "%int32_of_int"

external int_of_int64 : int64 -> int = "%int64_to_int"

external int_of_int32 : int32 -> int = "%int32_to_int"

external int64_of_int32 : int32 -> int64 = "%int64_of_int32"

let low_32_bits = int_of_int32 (int32_of_int64 4294967297L)

let sign_from_bit_31 = int_of_int32 (int32_of_int64 2147483648L)

let all_ones_32 = int_of_int32 (int32_of_int 4294967295)

let low_63_bits = int_of_int64 (-9223372036854775808L)

let sign_from_bit_62 = int_of_int64 4611686018427387904L

let sign_extended = int_of_int64 (int64_of_int32 (-1l))
