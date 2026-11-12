(* A recursive function that is not tail-recursive, applied to constants.
   Simplify does not unroll it. *)

external ( * ) : int -> int -> int = "%mulint"

external ( - ) : int -> int -> int = "%subint"

external ( = ) : int -> int -> bool = "%equal"

let rec power base exponent =
  if exponent = 0 then 1 else base * power base (exponent - 1)

let result = power 2 10
