(* A recursive function that returns a function of its own, which calls the
   recursive function. The closure returned holds the recursive function in a
   value slot; Simplify makes its code call the symbol of the recursive
   function. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

let rec count n = if n = 0 then fun b -> b else fun b -> count (n - 1) (b + 1)
