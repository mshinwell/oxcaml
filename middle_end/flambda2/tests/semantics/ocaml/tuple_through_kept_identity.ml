(* A pair given to a function that returns it and is never inlined, and then
   taken apart. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] keep pair = pair

let result =
  let a, b = keep (opaque 1, 2) in
  a + b
