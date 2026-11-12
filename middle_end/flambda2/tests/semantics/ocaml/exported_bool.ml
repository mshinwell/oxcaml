(* An exported predicate and an exported function that uses it twice. *)

external gt : int -> int -> bool = "%gtint"

external ( && ) : bool -> bool -> bool = "%sequand"

let is_pos x = gt x 0

let both x y = is_pos x && is_pos y
