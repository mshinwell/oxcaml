(* A pair built, passed to a function that swaps it, and taken apart. *)

external ( - ) : int -> int -> int = "%subint"

external opaque : 'a -> 'a = "%opaque"

let swap pair =
  let a, b = pair in
  b, a

let result =
  let x, y = swap (opaque 1, opaque 10) in
  x - y
