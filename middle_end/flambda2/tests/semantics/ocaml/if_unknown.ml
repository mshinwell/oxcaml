(* A conditional on a value that is not known, at the top of the unit. Simplify
   puts the handler of the continuation that defines the unit into that of the
   continuation the two branches go to, its only use. The validator inlines a
   continuation used once only where it is applied in the body of its own
   [Let_cont]. *)

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let result = if opaque 3 < 5 then 1 else 2
