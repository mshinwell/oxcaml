(* Division by a divisor that is not known and not zero: the test of the divisor
   stays. *)

external ( / ) : int -> int -> int = "%divint"

external opaque : 'a -> 'a = "%opaque"

let result = opaque 17 / opaque 5
