(* One function called twice: the first call is marked to be inlined and the
   second never to be. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let square_plus_one x = (x * x) + 1

let result =
  (square_plus_one [@inlined]) (opaque 3)
  + (square_plus_one [@inlined never]) (opaque 4)
