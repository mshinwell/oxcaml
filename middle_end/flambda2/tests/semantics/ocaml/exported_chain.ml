(* Three exported functions, each calling the one before twice. *)

external ( + ) : int -> int -> int = "%addint"

let f x = x + 1

let g x = f (f x)

let h x = g (g x)
