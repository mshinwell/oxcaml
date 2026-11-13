(* Two functions defined together with [let rec .. and ..], neither of which is
   recursive: the first calls the second, and the unit calls both. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let rec first x = second (x + 1)

and second x = x * 3

let result = first (opaque 2) + second 1
