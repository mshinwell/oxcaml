external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external code : char -> int = "%identity"

external ( - ) : int -> int -> int = "%subint"

val digit : char -> int option

val value : int option -> int

val result : int
