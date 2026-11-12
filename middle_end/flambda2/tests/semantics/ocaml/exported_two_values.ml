(* A unit that exports two values, the second computed from the first. Simplify
   computes both. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

let[@inline] square x = x * x

let nine = square 3

let result = nine + square 4
