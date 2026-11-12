(* A function made in the arm of a test, which uses a value that is not known
   and is computed before the test: its closure holds the value. Simplify binds
   the closure to a symbol before the test. *)

external ( + ) : int -> int -> int = "%addint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

let step = opaque 3

let advance = if step > 2 then fun position -> position + step else fun p -> p
