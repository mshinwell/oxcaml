(* A field read before a call that is kept and again after it. *)

external ( + ) : int -> int -> int = "%addint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] twice x = x + x

let around pair =
  let first = fst pair in
  let doubled = twice first in
  doubled + fst pair

let result = around (opaque 3, 0)
