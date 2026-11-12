(* Arithmetic that overflows wraps round, at the width of an OCaml integer, when
   Simplify computes it as when the machine does. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

let max_int = 4611686018427387903

let min_int = -4611686018427387904

let above_the_largest = max_int + 1 = min_int

let below_the_least = min_int - 1 = max_int

let twice_the_largest = max_int * 2

let the_least_squared = min_int * min_int

let the_largest_squared = max_int * max_int
