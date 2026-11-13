(* A function with a handler that raises another exception, inlined under a
   second handler. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

external raise : exn -> 'a = "%raise"

let[@inline] check x = if x < 0 then raise Not_found else x

let[@inline] guarded x =
  try check x with Not_found -> raise (Failure "negative")

let[@inline never] body x = try guarded x + 1 with Failure _ -> 500

let result = body (opaque 2) + body (opaque (0 - 2))
