(* The six comparisons of integers, at constants. Simplify inlines [compare_all]
   twice and folds everything to 61. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( <= ) : int -> int -> bool = "%lessequal"

external ( > ) : int -> int -> bool = "%greaterthan"

external ( >= ) : int -> int -> bool = "%greaterequal"

external ( = ) : int -> int -> bool = "%equal"

external ( <> ) : int -> int -> bool = "%notequal"

let[@inline] bit test weight = if test then weight else 0

let[@inline] compare_all a b =
  bit (a < b) 1
  + bit (a <= b) 2
  + bit (a > b) 4
  + bit (a >= b) 8
  + bit (a = b) 16
  + bit (a <> b) 32

let result = compare_all 3 4 + compare_all 5 5
