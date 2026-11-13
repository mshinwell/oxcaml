external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external code : char -> int = "%identity"

external unsafe_chr : int -> char = "%identity"

external ( - ) : int -> int -> int = "%subint"

external ( >= ) : 'a -> 'a -> bool = "%greaterequal"

external ( <= ) : 'a -> 'a -> bool = "%lessequal"

external ( && ) : bool -> bool -> bool = "%sequand"

val uppercase : char -> char

val result : int
