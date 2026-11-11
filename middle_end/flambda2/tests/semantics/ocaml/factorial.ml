(* A function that is recursive and not tail-recursive. *)

external ( * ) : int -> int -> int = "%mulint"

external ( - ) : int -> int -> int = "%subint"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

let rec factorial n = if n <= 1 then 1 else n * factorial (n - 1)

let result = factorial (opaque 5)
