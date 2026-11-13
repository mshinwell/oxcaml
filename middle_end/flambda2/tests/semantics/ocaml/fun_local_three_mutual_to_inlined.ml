(* Three local functions that call each other in a ring, each given to an
   inlined function. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] apply f x = f x

let run n =
  let rec zero k = if k = 0 then n else one (k - 1)
  and one k = if k = 0 then n + 1 else two (k - 1)
  and two k = if k = 0 then n + 2 else zero (k - 1) in
  apply zero 4 + apply one n + apply two 2

let result = run (opaque 4)
