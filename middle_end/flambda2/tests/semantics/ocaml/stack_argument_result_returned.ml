(* A function that allocates a pair on its stack, gives it to another function,
   and returns what that function returns. [total] takes a pair that may be on
   the stack, so [sum_with_next] allocates the pair in a region of its own,
   which it ends when the call has returned: the continuation that the call
   returns to ends the region and passes the result on. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] total (local_ p : int * int) =
  let a, b = p in
  a + b

let[@inline never] sum_with_next x =
  let sum = total (x, x + 1) in
  sum

let result = sum_with_next (opaque 3)
