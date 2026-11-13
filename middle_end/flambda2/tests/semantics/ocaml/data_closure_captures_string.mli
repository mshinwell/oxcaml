external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

val reader : string -> int -> int

val from_constant : int -> int

val from_unknown : int -> int

val result : int
