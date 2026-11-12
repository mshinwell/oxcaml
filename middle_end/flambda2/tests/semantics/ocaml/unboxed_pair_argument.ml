(* A function that takes an unboxed pair: its code has two parameters. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] sum #(a, b) = a + b

let result = sum #(opaque 3, 4)
