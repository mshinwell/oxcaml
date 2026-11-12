(* A function that never returns, called on two paths that the unit does not
   take, under no handler: Simplify gives the two calls no return
   continuation. *)

external ( + ) : int -> int -> int = "%addint"

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] fail () = raise Not_found

let result : int =
  (if opaque false then fail () else 3) + if opaque false then fail () else 4
