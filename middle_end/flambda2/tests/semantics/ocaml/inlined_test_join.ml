(* A function with a test, inlined at a call whose result is not used, before a
   [try]. The continuation that the call returns to is bound before the argument
   of the call is computed; the continuation where the two branches of the test
   meet is bound in the body of the function, after it, and applies the first.
   Simplify keeps the first, the validation the second. *)

external ( > ) : int -> int -> bool = "%greaterthan"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type pair =
  { x : int;
    y : int
  }

let[@inline] make p q = { x = p; y = (if q > q then opaque (-2) else p + 3) }

let result =
  let _ = make 8 (opaque (-3)) in
  try -3 + -1 with _ -> 8
