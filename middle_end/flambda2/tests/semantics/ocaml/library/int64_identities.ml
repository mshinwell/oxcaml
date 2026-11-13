(* Int64 operations with one operand written in the function, or the same
   operand twice. *)

let opaque = Sys.opaque_identity

let flag = opaque true

let[@inline] and_ones (x : int64) = Int64.logand x (-1L)

let[@inline] xor_self (x : int64) = Int64.logxor x x

let[@inline] sub_self (x : int64) = Int64.sub x x

let[@inline] mul_minus_one (x : int64) = Int64.mul x (-1L)

let[@inline] shift_zero (x : int64) = Int64.shift_left x 0

let and_ones_min = and_ones (-9223372036854775808L)

let and_ones_min_unknown = and_ones (opaque (-9223372036854775808L))

let and_ones_min_joined = and_ones (if flag then -9223372036854775808L else 0L)

let xor_self_min = xor_self (-9223372036854775808L)

let xor_self_min_unknown = xor_self (opaque (-9223372036854775808L))

let xor_self_min_joined = xor_self (if flag then -9223372036854775808L else 0L)

let sub_self_max = sub_self 9223372036854775807L

let sub_self_max_unknown = sub_self (opaque 9223372036854775807L)

let sub_self_max_joined = sub_self (if flag then 9223372036854775807L else 0L)

let mul_minus_one_min = mul_minus_one (-9223372036854775808L)

let mul_minus_one_min_unknown = mul_minus_one (opaque (-9223372036854775808L))

let mul_minus_one_min_joined =
  mul_minus_one (if flag then -9223372036854775808L else 0L)

let shift_zero_min = shift_zero (-9223372036854775808L)

let shift_zero_min_unknown = shift_zero (opaque (-9223372036854775808L))

let shift_zero_min_joined =
  shift_zero (if flag then -9223372036854775808L else 0L)
