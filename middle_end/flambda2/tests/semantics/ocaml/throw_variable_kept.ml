(* A function that raises the exception it is given, and stays a function. *)
external raise : exn -> 'a = "%raise"

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] throw_if_negative e n = if n < 0 then raise e else n

let result =
  (try throw_if_negative Not_found (opaque 3) with Not_found -> 100)
  + try throw_if_negative End_of_file (opaque (-3)) with End_of_file -> 200
