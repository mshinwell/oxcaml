(* Nativeint operations with one operand written in the function, or the same
   operand twice. *)

let opaque = Sys.opaque_identity

let flag = opaque true

let[@inline] and_ones (x : nativeint) = Nativeint.logand x (-1n)

let[@inline] xor_self (x : nativeint) = Nativeint.logxor x x

let[@inline] sub_self (x : nativeint) = Nativeint.sub x x

let[@inline] mul_minus_one (x : nativeint) = Nativeint.mul x (-1n)

let[@inline] shift_zero (x : nativeint) = Nativeint.shift_left x 0

let and_ones_min = and_ones (-9223372036854775808n)

let and_ones_min_unknown = and_ones (opaque (-9223372036854775808n))

let and_ones_min_joined = and_ones (if flag then -9223372036854775808n else 0n)

let xor_self_min = xor_self (-9223372036854775808n)

let xor_self_min_unknown = xor_self (opaque (-9223372036854775808n))

let xor_self_min_joined = xor_self (if flag then -9223372036854775808n else 0n)

let sub_self_max = sub_self 9223372036854775807n

let sub_self_max_unknown = sub_self (opaque 9223372036854775807n)

let sub_self_max_joined = sub_self (if flag then 9223372036854775807n else 0n)

let mul_minus_one_min = mul_minus_one (-9223372036854775808n)

let mul_minus_one_min_unknown = mul_minus_one (opaque (-9223372036854775808n))

let mul_minus_one_min_joined =
  mul_minus_one (if flag then -9223372036854775808n else 0n)

let shift_zero_min = shift_zero (-9223372036854775808n)

let shift_zero_min_unknown = shift_zero (opaque (-9223372036854775808n))

let shift_zero_min_joined =
  shift_zero (if flag then -9223372036854775808n else 0n)
