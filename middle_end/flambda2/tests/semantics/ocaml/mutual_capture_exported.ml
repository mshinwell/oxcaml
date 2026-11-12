(* Two functions that call each other and read a value that is not known until
   the unit runs, both exported; the unit calls both. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let step = opaque 3

let rec shrink n = if n < step then n else grow (n - step - step)

and grow n = if n < 0 then n else shrink (n + step)

let result = shrink 10 + grow 1
