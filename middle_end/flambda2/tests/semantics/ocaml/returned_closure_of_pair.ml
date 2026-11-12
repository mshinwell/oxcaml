(* A function that returns one closure of a pair of functions that call each
   other, applied at once. *)

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let make a =
  let rec g x = if x = 0 then a else h (x - 1) and h x = g x in
  g

let result = (make (opaque 5)) 3
