(* The bitwise operations on a number that Simplify does not know. *)

external ( + ) : int -> int -> int = "%addint"

external ( land ) : int -> int -> int = "%andint"

external ( lor ) : int -> int -> int = "%orint"

external ( lxor ) : int -> int -> int = "%xorint"

external opaque : 'a -> 'a = "%opaque"

let result =
  let x = opaque 12 in
  (x land 10) + (x lor 3) + (x lxor 5)
