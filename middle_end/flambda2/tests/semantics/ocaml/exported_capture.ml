(* An exported function that uses a value of the module which is not known until
   the module is run: it is a value slot of the closure. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let base = opaque 10

let add x = x + base

let result = add 1
