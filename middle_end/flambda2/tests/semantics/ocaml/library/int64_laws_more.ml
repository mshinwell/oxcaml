(* More laws of the integers on Int64 numbers: one that holds whatever the
   width, and three that fail at the ends of the range. *)

let opaque = Sys.opaque_identity

let flag = opaque true

let[@inline] shift_there_and_back (x : int64) =
  Int64.shift_right (Int64.shift_left x 1) 1 = x

let[@inline] add_then_sub (x : int64) (y : int64) =
  Int64.sub (Int64.add x y) y = x

let[@inline] sum_is_positive (x : int64) (y : int64) = Int64.add x y > 0L

let[@inline] difference_is_negative (x : int64) (y : int64) = Int64.sub x y < 0L

let shift_there_and_back_max = shift_there_and_back 9223372036854775807L

let shift_there_and_back_max_unknown =
  shift_there_and_back (opaque 9223372036854775807L)

let shift_there_and_back_max_joined =
  shift_there_and_back (if flag then 9223372036854775807L else 0L)

let add_then_sub_max_max =
  add_then_sub 9223372036854775807L 9223372036854775807L

let add_then_sub_max_max_unknown =
  add_then_sub (opaque 9223372036854775807L) (opaque 9223372036854775807L)

let add_then_sub_max_max_joined =
  add_then_sub (if flag then 9223372036854775807L else 0L) 9223372036854775807L

let sum_is_positive_max_one = sum_is_positive 9223372036854775807L 1L

let sum_is_positive_max_one_unknown =
  sum_is_positive (opaque 9223372036854775807L) (opaque 1L)

let sum_is_positive_max_one_joined =
  sum_is_positive (if flag then 9223372036854775807L else 0L) 1L

let difference_is_negative_min_one =
  difference_is_negative (-9223372036854775808L) 1L

let difference_is_negative_min_one_unknown =
  difference_is_negative (opaque (-9223372036854775808L)) (opaque 1L)

let difference_is_negative_min_one_joined =
  difference_is_negative (if flag then -9223372036854775808L else 0L) 1L
