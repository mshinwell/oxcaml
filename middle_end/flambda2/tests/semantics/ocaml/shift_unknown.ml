(* Shifts of a number that Simplify does not know, by constants. *)

external ( + ) : int -> int -> int = "%addint"

external ( lsl ) : int -> int -> int = "%lslint"

external ( lsr ) : int -> int -> int = "%lsrint"

external ( asr ) : int -> int -> int = "%asrint"

external opaque : 'a -> 'a = "%opaque"

let result =
  let x = opaque 5 in
  (x lsl 2) + (x lsr 1) + (x asr 1)
