(* The first unit of a pair: two functions that call each other, which are one
   set of closures with two function slots. *)

external ( - ) : int -> int -> int = "%subint"

external ( == ) : int -> int -> bool = "%eq"

let rec even n = if n == 0 then true else odd (n - 1)

and odd n = if n == 0 then false else even (n - 1)
