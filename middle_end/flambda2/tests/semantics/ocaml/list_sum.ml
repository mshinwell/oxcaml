(* A list written out and summed by a recursive function. Simplify makes the
   closure of [sum] a symbol and leaves the calls. *)

external ( + ) : int -> int -> int = "%addint"

let rec sum list = match list with [] -> 0 | x :: rest -> x + sum rest

let result = sum [1; 2; 3]
