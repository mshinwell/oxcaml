(* A lowercase letter made uppercase by arithmetic on its code. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external code : char -> int = "%identity"

external unsafe_chr : int -> char = "%identity"

external ( - ) : int -> int -> int = "%subint"

external ( >= ) : 'a -> 'a -> bool = "%greaterequal"

external ( <= ) : 'a -> 'a -> bool = "%lessequal"

external ( && ) : bool -> bool -> bool = "%sequand"

let uppercase c = if c >= 'a' && c <= 'z' then unsafe_chr (code c - 32) else c

let result =
  code (uppercase 'a')
  + code (uppercase (opaque 'z'))
  + code (uppercase (opaque '!'))
