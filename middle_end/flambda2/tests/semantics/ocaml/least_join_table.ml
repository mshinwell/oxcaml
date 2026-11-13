(* A match on a value chosen by a test; its arms give numbers of no rule. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type side =
  | Left
  | Right
  | Both

let[@inline never] pick c a b =
  let x = if c then a else b in
  match x with Left -> 7 | Right -> 1 | Both -> 4

let result = pick (opaque true) Left Both + (pick (opaque false) Left Both * 10)
