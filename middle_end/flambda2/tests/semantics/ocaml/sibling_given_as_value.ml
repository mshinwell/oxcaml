(* Two functions that call each other; the first gives the second, as a value,
   to a function that is kept. *)

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] call f x = f x

let rec count_down n = if n = 0 then 0 else call restart (n - 1)

and restart n = count_down n

let result = count_down (opaque 3)
