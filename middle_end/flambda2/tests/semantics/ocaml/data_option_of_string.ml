(* An option that holds a string, with a default. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

let or_default o = match o with Some s -> s | None -> "default"

let result =
  length (or_default (Some "abc"))
  + length (or_default (opaque None))
  + length (or_default (opaque (Some "")))
