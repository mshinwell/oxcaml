(* A function marked [@inline] with [@inlined never] at one of its calls. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] f x = (x * 3) + 1

let result =
  (f [@inlined never]) 5 + f (opaque 7) + (f [@inlined never]) (opaque 1)
