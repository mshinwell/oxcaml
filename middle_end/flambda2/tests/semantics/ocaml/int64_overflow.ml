(* Arithmetic on 64-bit integers wraps round at 64 bits. *)

external add : int64 -> int64 -> int64 = "%int64_add"

external mul : int64 -> int64 -> int64 = "%int64_mul"

external neg : int64 -> int64 = "%int64_neg"

external equal : int64 -> int64 -> bool = "%equal"

external to_int : int64 -> int = "%int64_to_int"

let above_the_largest =
  equal (add 9223372036854775807L 1L) (-9223372036854775808L)

let two_to_the_64 = to_int (mul 4294967296L 4294967296L)

let the_least_negated =
  equal (neg (-9223372036854775808L)) (-9223372036854775808L)
