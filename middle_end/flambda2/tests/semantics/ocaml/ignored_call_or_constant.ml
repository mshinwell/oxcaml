(* A test whose branches are a call and a constant, with nothing using what it
   gives. Simplify removes the parameter of the continuation after the test: the
   branch of the constant applies it to nothing, and the call, which gives its
   result to what it returns to, returns to a new continuation that takes the
   result and applies the old one to nothing. The two functions are exported, so
   that they stay functions. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] twice (x : int) : int = x + x

let[@inline never] ignored (c : bool) (x : int) : int =
  let _ = if c then twice x else 8 in
  x + 1

let result = ignored (opaque true) 3
