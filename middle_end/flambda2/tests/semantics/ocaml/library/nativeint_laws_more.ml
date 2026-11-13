(* More laws of the integers on Nativeint numbers: one that holds whatever the
   width, and three that fail at the ends of the range. *)

let opaque = Sys.opaque_identity

let flag = opaque true

let[@inline] shift_there_and_back (x : nativeint) =
  Nativeint.shift_right (Nativeint.shift_left x 1) 1 = x

let[@inline] add_then_sub (x : nativeint) (y : nativeint) =
  Nativeint.sub (Nativeint.add x y) y = x

let[@inline] sum_is_positive (x : nativeint) (y : nativeint) =
  Nativeint.add x y > 0n

let[@inline] difference_is_negative (x : nativeint) (y : nativeint) =
  Nativeint.sub x y < 0n

let shift_there_and_back_max = shift_there_and_back 9223372036854775807n

let shift_there_and_back_max_unknown =
  shift_there_and_back (opaque 9223372036854775807n)

let shift_there_and_back_max_joined =
  shift_there_and_back (if flag then 9223372036854775807n else 0n)

let add_then_sub_max_max =
  add_then_sub 9223372036854775807n 9223372036854775807n

let add_then_sub_max_max_unknown =
  add_then_sub (opaque 9223372036854775807n) (opaque 9223372036854775807n)

let add_then_sub_max_max_joined =
  add_then_sub (if flag then 9223372036854775807n else 0n) 9223372036854775807n

let sum_is_positive_max_one = sum_is_positive 9223372036854775807n 1n

let sum_is_positive_max_one_unknown =
  sum_is_positive (opaque 9223372036854775807n) (opaque 1n)

let sum_is_positive_max_one_joined =
  sum_is_positive (if flag then 9223372036854775807n else 0n) 1n

let difference_is_negative_min_one =
  difference_is_negative (-9223372036854775808n) 1n

let difference_is_negative_min_one_unknown =
  difference_is_negative (opaque (-9223372036854775808n)) (opaque 1n)

let difference_is_negative_min_one_joined =
  difference_is_negative (if flag then -9223372036854775808n else 0n) 1n
