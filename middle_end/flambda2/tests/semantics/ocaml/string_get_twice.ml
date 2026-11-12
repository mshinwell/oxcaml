(* Two reads of one string at one unknown index, one after the other. *)

external get : string -> int -> char = "%string_safe_get"

external code : char -> int = "%identity"

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let result =
  let s = opaque "hello" in
  let i = opaque 1 in
  code (get s i) + code (get s i)
