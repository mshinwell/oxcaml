(* The same boxed sum computed twice. *)

external ( + ) : int -> int -> int = "%addint"

external add : int64 -> int64 -> int64 = "%int64_add"

external to_int : int64 -> int = "%int64_to_int"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] doubled x =
  let a = add x 1L in
  let b = add x 1L in
  to_int a + to_int b

let result = doubled (opaque 20L)
