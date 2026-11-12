(* Two arrays with no element compared by [==]. The front end makes one symbol
   of the two, so an allocated value is compared with itself, and the model
   gives that no value. *)

external ( == ) : 'a -> 'a -> bool = "%eq"

external opaque : 'a -> 'a = "%opaque"

let a : int array = [||]

let b : int array = [||]

let result = if opaque a == opaque b then 1 else 0
