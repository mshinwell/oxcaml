(* A recursive function, exported and not called. *)

external ( = ) : int -> int -> bool = "%equal"

external ( * ) : int -> int -> int = "%mulint"

external ( - ) : int -> int -> int = "%subint"

let rec fact n = if n = 0 then 1 else n * fact (n - 1)
