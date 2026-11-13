(* The boolean that a call returns is tested, and the argument of that call is
   the result of another call. Neither function is inlined, and each is called
   twice. The first call returns to a continuation that makes the second. The
   front end binds the continuation that tests before that one; Simplify, which
   untags the boolean, binds it at the second call, in the handler of that
   one. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] next n = n + 1

let[@inline never] small n = n < 10

let result =
  (if small (next (opaque 4)) then 1 else 2)
  + if small (next (opaque 40)) then 10 else 20
