(* The value of a digit character, as an option. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external code : char -> int = "%identity"

external ( - ) : int -> int -> int = "%subint"

let digit c = match c with '0' .. '9' -> Some (code c - code '0') | _ -> None

let value o = match o with Some n -> n | None -> 100

let result =
  value (digit '7') + value (digit (opaque '3')) + value (digit (opaque 'x'))
