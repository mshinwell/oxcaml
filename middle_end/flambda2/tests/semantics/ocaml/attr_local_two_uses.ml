(* A function marked [@local], used in the last position of two arms. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] body x y =
  let[@local] finish a b = (a * 10) + b + x in
  if x < y then finish x y else finish y x

let result = body (opaque 3) 5 + body 8 (opaque 2)
