external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external length : string -> int = "%string_length"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

val vowels : string -> int -> int -> int

val result : int
