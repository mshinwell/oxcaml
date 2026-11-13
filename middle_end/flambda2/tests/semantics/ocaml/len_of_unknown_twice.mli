external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

external ( * ) : int -> int -> int = "%mulint"

val area : string -> int

val result : int
