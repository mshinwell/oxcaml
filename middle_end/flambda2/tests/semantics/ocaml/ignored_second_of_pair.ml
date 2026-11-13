(* A test whose branches are a call that returns two values and a pair of
   constants, with only the first of the two used after it. Simplify removes
   the second parameter of the continuation after the test, and the call
   returns to a new continuation that takes the two results and passes the
   first on. The functions are exported, so that they stay functions. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] both (x : int) : #(int * int) = #(x, x + 1)

let[@inline never] first_of (c : bool) (x : int) : int =
  let #(a, _b) = if c then both x else #(8, 9) in
  a + 1

let result = first_of (opaque true) 3
