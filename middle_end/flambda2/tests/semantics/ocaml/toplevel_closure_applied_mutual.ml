(* A closure over a value that is not known until the unit runs, given to an
   inlined function at toplevel, in a unit with two functions that call each
   other. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

let rec even n = if n = 0 then 1 else odd (n - 1)

and odd n = if n = 0 then 0 else even (n - 1)

let base = opaque 10

let add_base x = x + base

let result = apply add_base 1 + apply add_base (even 4)
