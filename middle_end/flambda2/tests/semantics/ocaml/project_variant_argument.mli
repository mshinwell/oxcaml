type shape =
  | Circle of int
  | Rect of int * int

val height : shape -> int

val rect_height : int -> int -> int

val result : int
