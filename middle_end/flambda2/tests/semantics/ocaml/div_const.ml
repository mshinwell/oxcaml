(* Division and remainder by a constant that is not zero: no test of the divisor
   is left. *)

external ( + ) : int -> int -> int = "%addint"

external ( / ) : int -> int -> int = "%divint"

external ( mod ) : int -> int -> int = "%modint"

external opaque : 'a -> 'a = "%opaque"

let result =
  let x = opaque 17 in
  (x / 5) + (x mod 5)
