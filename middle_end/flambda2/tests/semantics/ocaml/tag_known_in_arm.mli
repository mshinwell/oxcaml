type amount =
  | Free
  | Fixed of int
  | Percent of int

val value_of : amount -> int -> int

val price : amount -> int -> int

val result : int
