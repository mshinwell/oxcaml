(* Two functions that call each other, and another name of the first, all
   exported; the unit calls it under that name. *)

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let rec ping n = if n = 0 then 0 else pong (n - 1)

and pong n = if n = 0 then 1 else ping (n - 1)

let start = ping

let result = start (opaque 5)
