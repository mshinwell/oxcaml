(* Two exported names of one pair, one on each path of a test. *)

external fst : 'a * 'b -> 'a = "%field0_immut"

external opaque : 'a -> 'a = "%opaque"

let default = opaque 1, opaque 2

let fallback = default

let pick flag =
  let pair = if flag then default else fallback in
  fst pair

let result = pick (opaque true)
