(* A character read as a number: the identity, which leaves nothing. *)

external code : char -> int = "%identity"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let result = code (opaque 'a') + 1
