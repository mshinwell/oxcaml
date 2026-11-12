(* An optional argument with a default is an option that the function matches
   on. Simplify inlines [scale] twice and resolves both matches, one on [None]
   and one on [Some 3]. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] scale ?(by = 2) x = x * by

let result = scale (opaque 5) + scale ~by:3 (opaque 5)
