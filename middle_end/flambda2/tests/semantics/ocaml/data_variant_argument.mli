external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

type label =
  | Anonymous
  | Named of string
  | Numbered of int

val size : label -> int

val result : int
