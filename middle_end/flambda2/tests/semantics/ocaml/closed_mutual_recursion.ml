(* Two functions that call each other and are closed over one variable: each
   reads the variable, or the other function, from its own closure. *)

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let f a =
  let rec g x = if x = 0 then a else h (x - 1) and h x = g x in
  g 3

let result = f (opaque 5)
