(* Two closures, one in each arm of a test, then called. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] body c x =
  let f = if c then fun y -> y + x else fun y -> y * x in
  f 10

let result = body (opaque true) 3 + body false (opaque 4) + body true 5
