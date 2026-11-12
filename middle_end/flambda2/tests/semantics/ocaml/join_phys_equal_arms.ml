(* One of two values chosen by a test of whether they are the same. *)

external ( == ) : 'a -> 'a -> bool = "%eq"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] either a b = if a == b then a else b

let result = either (opaque 3) 3 + either (opaque 3) 4
