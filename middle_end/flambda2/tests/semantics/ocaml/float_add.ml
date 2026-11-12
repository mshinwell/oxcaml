(* Floating-point arithmetic. *)

external ( +. ) : float -> float -> float = "%addfloat"

external opaque : 'a -> 'a = "%opaque"

let result = opaque 1.5 +. 2.25
