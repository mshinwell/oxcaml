(* A test whose two branches are calls, with nothing using what they give: each
   call returns to a new continuation of its own, which takes the result and
   applies the continuation after the test to nothing. The functions are
   exported, so that they stay functions. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] twice (x : int) : int = x + x

let[@inline never] thrice (x : int) : int = x + x + x

let[@inline never] ignored (c : bool) (x : int) : int =
  let _ = if c then twice x else thrice x in
  x + 1

let result = ignored (opaque true) 3
