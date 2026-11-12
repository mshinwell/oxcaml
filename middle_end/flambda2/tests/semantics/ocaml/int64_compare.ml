(* Comparisons of boxed 64-bit integers at constants. Simplify folds the whole
   to [true]. *)

external add : int64 -> int64 -> int64 = "%int64_add"

external less_than : int64 -> int64 -> bool = "%lessthan"

external equal : int64 -> int64 -> bool = "%equal"

external ( && ) : bool -> bool -> bool = "%sequand"

let[@inline] between low x high = less_than low x && less_than x high

let result = between 1L (add 2L 3L) 10L && equal (add 1L 1L) 2L
