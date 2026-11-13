(* Ranges with an alias: the value of a hexadecimal digit. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

external code : char -> int = "%identity"

let[@inline never] digit c =
  match c with
  | '0' .. '9' as d -> code d - 48
  | 'a' .. 'f' as d -> code d - 87
  | 'A' .. 'F' as d -> code d - 55
  | _ -> -1

let result =
  digit (opaque '7')
  + (digit (opaque 'c') * 16)
  + (digit (opaque 'F') * 256)
  + (digit (opaque 'g') * 4096)
