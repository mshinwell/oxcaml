(* A variant with a constructor that holds a string. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

type label =
  | Anonymous
  | Named of string
  | Numbered of int

let size l =
  match l with Anonymous -> 0 | Named s -> length s | Numbered n -> n

let result =
  size (Named "hello")
  + size (opaque (Named "abc"))
  + size (opaque Anonymous)
  + size (Numbered 4)
