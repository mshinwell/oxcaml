(* A function inlined at two arguments that are not known. The two copies of its
   body bind the same names in the term before, one in the scope of the other;
   Simplify gives each copy names of its own. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] square x = x * x

let result = square (opaque 3) + square (opaque 4)
