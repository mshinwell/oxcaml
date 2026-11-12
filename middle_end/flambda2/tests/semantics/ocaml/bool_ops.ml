(* [&&] and [||] are conditionals and [not] is a primitive. Simplify inlines the
   two functions and folds the whole to [false]. *)

external not : bool -> bool = "%boolnot"

external ( && ) : bool -> bool -> bool = "%sequand"

external ( || ) : bool -> bool -> bool = "%sequor"

let[@inline] implies a b = (not a) || b

let[@inline] xor a b = (a || b) && not (a && b)

let result = implies (xor true false) (xor true true)
