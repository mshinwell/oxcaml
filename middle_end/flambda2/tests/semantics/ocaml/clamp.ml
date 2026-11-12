(* Two comparisons one after the other, at three constants. Simplify inlines
   [clamp] three times and folds every comparison. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

let[@inline] clamp ~low ~high x =
  if x < low then low else if x > high then high else x

let result =
  clamp ~low:0 ~high:10 (-5) + clamp ~low:0 ~high:10 5
  + clamp ~low:0 ~high:10 50
