(* A list of constant strings, and the sum of their lengths by a recursive
   function. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

let rec total words acc =
  match words with [] -> acc | w :: rest -> total rest (acc + length w)

let words = ["one"; "three"; ""; "seventeen"]

let result = total (opaque words) 0
