external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

val shorter : string -> string -> string

val result : int
