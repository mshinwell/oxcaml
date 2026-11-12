(* [~-], [succ] and [pred], which are an integer subtraction and two
   additions. *)

external ( ~- ) : int -> int = "%negint"

external succ : int -> int = "%succint"

external pred : int -> int = "%predint"

external opaque : 'a -> 'a = "%opaque"

let result = succ (pred (-opaque 5))
