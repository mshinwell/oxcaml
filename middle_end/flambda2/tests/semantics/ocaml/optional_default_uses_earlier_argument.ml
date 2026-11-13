(* Two optional arguments, the default of the second computed from the first;
   each is omitted or given in turn. *)
external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

let clamp ?(low = 0) ?(high = low + 10) x =
  if x < low then low else if x < high then x else high

let both_omitted = clamp 5

let low_given = clamp ~low:20 5

let high_given = clamp ~high:3 5

let both_given = clamp ~low:2 ~high:4 9

let high_then_low = clamp ~high:40 ~low:30 100
