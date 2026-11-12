(* A function that never returns, called in a function that the unit keeps and
   calls twice, each time under a handler: Simplify gives the call in the
   function no return continuation. *)

external ( + ) : int -> int -> int = "%addint"

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] fail () = raise Not_found

let[@inline never] f x = if x then fail () else 1

let result =
  (try f (opaque true) with _ -> 2) + try f (opaque false) with _ -> 3
