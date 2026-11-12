(* A local closure given twice to an exported function that applies its argument
   and is inlined, in a unit that also has two functions that call each other.
   Simplify makes the two calls direct and inlines them, and the code of [run]
   is left with the additions. The closure is bound by a [Let] in the body of
   code and is one of a set whose function slot is named: the validation follows
   aliases there at its second asking. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

let rec even n = if n = 0 then 1 else odd (n - 1)

and odd n = if n = 0 then 0 else even (n - 1)

let run n =
  let add_n x = x + n in
  apply add_n 1 + apply add_n (even n)

let result = run (opaque 10)
