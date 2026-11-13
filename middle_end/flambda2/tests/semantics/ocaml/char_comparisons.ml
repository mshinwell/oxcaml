(* Characters compared for order and for equality. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

external ( < ) : 'a -> 'a -> bool = "%lessthan"

external ( = ) : 'a -> 'a -> bool = "%equal"

external compare : 'a -> 'a -> int = "%compare"

let order (a : char) (b : char) = if a < b then 1 else if a = b then 2 else 3

let result =
  order 'a' 'b'
  + order (opaque 'z') 'z'
  + order (opaque 'q') 'c'
  + compare 'a' (opaque 'b')
