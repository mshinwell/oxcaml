external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

val apply : ('a -> 'b) -> 'a -> 'b

val run : int option -> int -> int

val result : int
