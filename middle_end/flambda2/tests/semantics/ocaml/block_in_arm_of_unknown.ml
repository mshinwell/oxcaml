(* An option made in the arm of a test from a value that is not known and is
   computed before the test. Simplify binds the block to a symbol before the
   test, and the arm gives the symbol. *)

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type 'a option =
  | None
  | Some of 'a

let limit = opaque 3

let above = if limit > 2 then Some limit else None
