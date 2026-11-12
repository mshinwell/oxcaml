(* Division by a divisor that is not known, in a handler: the test of the
   divisor raises [Division_by_zero]. *)

external ( / ) : int -> int -> int = "%divint"

external opaque : 'a -> 'a = "%opaque"

let result = try opaque 7 / opaque 0 with _ -> -1
