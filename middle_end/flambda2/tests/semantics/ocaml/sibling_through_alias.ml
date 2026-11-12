(* Two functions that call each other, the first through a local name of the
   second. *)

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let rec walk n =
  let next = step in
  if n = 0 then 0 else next n

and step n = walk (n - 1)

let result = walk (opaque 4)
