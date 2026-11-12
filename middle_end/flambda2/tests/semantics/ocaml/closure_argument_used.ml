(* A local function given to a function that calls its argument and is
   inlined. *)

external ( + ) : int -> int -> int = "%addint"

let apply h x = h x

let f x =
  let g y = y + x in
  apply g x

external opaque : 'a -> 'a = "%opaque"

let result = f (opaque 3)
