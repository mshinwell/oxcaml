(* An exported function with a conditional on its arguments. *)

external ( < ) : int -> int -> bool = "%lessthan"

let max a b = if a < b then b else a
