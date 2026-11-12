(* A function that raises, inlined in a handler. *)

external raise : exn -> 'a = "%raise"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline] check x = if x < 0 then raise Not_found else x

let result = try check (opaque (-1)) with _ -> 0
