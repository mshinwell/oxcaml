(* A match of three cases, two of them calls and one a constant, with nothing
   using what it gives. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type choice =
  | Left
  | Middle
  | Right

let[@inline never] twice (x : int) : int = x + x

let[@inline never] ignored (c : choice) (x : int) : int =
  let _ =
    match c with Left -> twice x | Middle -> 8 | Right -> twice (x + 1)
  in
  x + 1

let result = ignored (opaque Right) 3
