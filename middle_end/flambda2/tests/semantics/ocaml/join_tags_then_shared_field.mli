type side =
  | Left of int
  | Right of int
  | Neither

val place : bool -> int -> side

val carried : bool -> int -> int

val result : int
