(* A read with no check under a test of the index against the length, written in
   the unit. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external unsafe_get : string -> int -> char = "%string_unsafe_get"

external code : char -> int = "%identity"

external length : string -> int = "%string_length"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

external ( <= ) : 'a -> 'a -> bool = "%lessequal"

external ( && ) : bool -> bool -> bool = "%sequand"

let char_or s i d = if 0 <= i && i < length s then code (unsafe_get s i) else d

let result = char_or "hello" (opaque 1) 0 + char_or (opaque "world") 5 1000
