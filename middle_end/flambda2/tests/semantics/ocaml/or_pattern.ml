(* A match with or-patterns on constant constructors. *)

external ( + ) : int -> int -> int = "%addint"

type day =
  | Mon
  | Tue
  | Wed
  | Thu
  | Fri
  | Sat
  | Sun

let[@inline] hours day =
  match day with Sat | Sun -> 0 | Fri -> 6 | Mon | Tue | Wed | Thu -> 8

let result = hours Mon + hours Fri + hours Sun
