external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

external length : string -> int = "%string_length"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

external ( <= ) : 'a -> 'a -> bool = "%lessequal"

external ( && ) : bool -> bool -> bool = "%sequand"

val char_or : string -> int -> int -> int

val result : int
