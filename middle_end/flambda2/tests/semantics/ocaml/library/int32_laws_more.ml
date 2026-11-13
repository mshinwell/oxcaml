(* More laws of the integers on Int32 numbers: one that holds whatever the
   width, and three that fail at the ends of the range. *)

let opaque = Sys.opaque_identity

let flag = opaque true

let[@inline] shift_there_and_back (x : int32) =
  Int32.shift_right (Int32.shift_left x 1) 1 = x

let[@inline] add_then_sub (x : int32) (y : int32) =
  Int32.sub (Int32.add x y) y = x

let[@inline] sum_is_positive (x : int32) (y : int32) = Int32.add x y > 0l

let[@inline] difference_is_negative (x : int32) (y : int32) = Int32.sub x y < 0l

let shift_there_and_back_max = shift_there_and_back 2147483647l

let shift_there_and_back_max_unknown = shift_there_and_back (opaque 2147483647l)

let shift_there_and_back_max_joined =
  shift_there_and_back (if flag then 2147483647l else 0l)

let add_then_sub_max_max = add_then_sub 2147483647l 2147483647l

let add_then_sub_max_max_unknown =
  add_then_sub (opaque 2147483647l) (opaque 2147483647l)

let add_then_sub_max_max_joined =
  add_then_sub (if flag then 2147483647l else 0l) 2147483647l

let sum_is_positive_max_one = sum_is_positive 2147483647l 1l

let sum_is_positive_max_one_unknown =
  sum_is_positive (opaque 2147483647l) (opaque 1l)

let sum_is_positive_max_one_joined =
  sum_is_positive (if flag then 2147483647l else 0l) 1l

let difference_is_negative_min_one = difference_is_negative (-2147483648l) 1l

let difference_is_negative_min_one_unknown =
  difference_is_negative (opaque (-2147483648l)) (opaque 1l)

let difference_is_negative_min_one_joined =
  difference_is_negative (if flag then -2147483648l else 0l) 1l
