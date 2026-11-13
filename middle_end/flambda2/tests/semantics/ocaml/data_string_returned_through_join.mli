external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

type entry =
  { key : string;
    weight : int
  }

val choose : bool -> 'a -> 'a -> 'a

val result : int
