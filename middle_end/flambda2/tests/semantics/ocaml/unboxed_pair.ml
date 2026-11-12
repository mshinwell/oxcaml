(* A function that returns an unboxed pair. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] both x = #(x, x + 1)

let result =
  let #(a, b) = both (opaque 3) in
  a + b
