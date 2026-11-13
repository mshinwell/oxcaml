(* An inlined function that raises in the arm that the call does not take. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

external raise : exn -> 'a = "%raise"

let[@inline] f flag x = if flag then raise Not_found else x + 1

let[@inline never] body x =
  try f false x + f (x < 0) x with Not_found -> 0 - 100

let result = body (opaque 5) + body (opaque (0 - 5))
