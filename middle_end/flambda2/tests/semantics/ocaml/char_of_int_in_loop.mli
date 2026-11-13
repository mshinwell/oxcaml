external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

external unsafe_chr : int -> char = "%identity"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

external ( = ) : 'a -> 'a -> bool = "%equal"

val count : int -> int -> int

val result : int
