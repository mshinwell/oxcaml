external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

external ( = ) : 'a -> 'a -> bool = "%equal"

external compare : 'a -> 'a -> int = "%compare"

val order : char -> char -> int

val result : int
