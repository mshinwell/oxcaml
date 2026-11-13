(* Two tests one after the other, each with a call in one branch and a constant
   in the other, and nothing using what either gives. Simplify removes the
   parameter of the continuation after each test, and each call returns to a new
   continuation that takes the result and applies the old one to nothing. The
   functions are exported, so that they stay functions. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] twice (x : int) : int = x + x

let[@inline never] ignored (c : bool) (d : bool) (x : int) : int =
  let _ = if c then twice x else 8 in
  let _ = if d then 9 else twice (x + 1) in
  x + 1

let result = ignored (opaque true) (opaque false) 3
