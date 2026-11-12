(* A constant pair on each arm of a test, taken apart at once. Result: 4. *)

external opaque : 'a -> 'a = "%opaque"

let[@inline] f x = if x then 4, true else 0, false

let result = match f (opaque true) with n, b -> if b then n else 7
