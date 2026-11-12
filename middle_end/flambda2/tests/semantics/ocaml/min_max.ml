(* [min] and [max] at constants. Simplify inlines both and folds the
   comparisons. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

let[@inline] min a b = if a < b then a else b

let[@inline] max a b = if a < b then b else a

let result = min 3 7 + max 3 7
