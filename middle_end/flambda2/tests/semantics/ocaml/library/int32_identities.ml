(* Int32 operations with one operand written in the function, or the same
   operand twice. *)

let opaque = Sys.opaque_identity

let flag = opaque true

let[@inline] and_ones (x : int32) = Int32.logand x (-1l)

let[@inline] xor_self (x : int32) = Int32.logxor x x

let[@inline] sub_self (x : int32) = Int32.sub x x

let[@inline] mul_minus_one (x : int32) = Int32.mul x (-1l)

let[@inline] shift_zero (x : int32) = Int32.shift_left x 0

let and_ones_min = and_ones (-2147483648l)

let and_ones_min_unknown = and_ones (opaque (-2147483648l))

let and_ones_min_joined = and_ones (if flag then -2147483648l else 0l)

let xor_self_min = xor_self (-2147483648l)

let xor_self_min_unknown = xor_self (opaque (-2147483648l))

let xor_self_min_joined = xor_self (if flag then -2147483648l else 0l)

let sub_self_max = sub_self 2147483647l

let sub_self_max_unknown = sub_self (opaque 2147483647l)

let sub_self_max_joined = sub_self (if flag then 2147483647l else 0l)

let mul_minus_one_min = mul_minus_one (-2147483648l)

let mul_minus_one_min_unknown = mul_minus_one (opaque (-2147483648l))

let mul_minus_one_min_joined = mul_minus_one (if flag then -2147483648l else 0l)

let shift_zero_min = shift_zero (-2147483648l)

let shift_zero_min_unknown = shift_zero (opaque (-2147483648l))

let shift_zero_min_joined = shift_zero (if flag then -2147483648l else 0l)
