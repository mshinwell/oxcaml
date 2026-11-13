(* A recursive function that calls itself through a closure it makes at each
   turn. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let rec depth n =
  let next = fun k -> depth k in
  if n = 0 then 0 else 1 + next (n - 1)

let result = depth 6 + depth (opaque 3)
