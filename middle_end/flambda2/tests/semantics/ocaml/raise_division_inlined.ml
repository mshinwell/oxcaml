(* A division inlined with a divisor that is zero at one call. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( / ) : int -> int -> int = "%divint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] ratio a b = a / b

let[@inline never] body a b = try ratio a b with Division_by_zero -> 0 - 1

let result =
  body 20 (opaque 4)
  + body (opaque 7) 0
  + try ratio 9 0 with Division_by_zero -> 77
