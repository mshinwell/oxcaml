(* Everything is known: Simplify inlines the calls and folds the arithmetic and
   the comparison, and the unit comes to a constant. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

let square x = x * x

let clamp x = if x < 0 then 0 else if 100 < x then 100 else x

let result = clamp (square 7 + square 8)
