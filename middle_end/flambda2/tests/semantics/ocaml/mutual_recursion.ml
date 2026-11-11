(* Two functions that call each other: a set of closures of two functions. *)

external ( - ) : int -> int -> int = "%subint"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

let rec even n = if n <= 0 then true else odd (n - 1)

and odd n = if n <= 0 then false else even (n - 1)

let result = even (opaque 10)
