(* An exported function given to another: the call of the argument is a call of
   a symbol once the first call is inlined. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let succ x = x + 1

let apply f x = f x

let result = apply succ (opaque 3)
