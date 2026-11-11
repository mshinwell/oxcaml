(* Two exported functions, the second of which calls the first: both closures
   become symbols, and the code of the second no longer reads the first out of
   its own closure. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let succ x = x + 1

let double_succ x = succ x * 2

let result = double_succ (opaque 3)
