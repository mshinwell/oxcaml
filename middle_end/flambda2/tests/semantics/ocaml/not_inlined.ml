(* A function that is not inlined and not exported, called twice: the two calls
   stay, and are made direct. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] square_plus_one x = (x * x) + 1

let result = square_plus_one (opaque 3) + square_plus_one (opaque 4)
