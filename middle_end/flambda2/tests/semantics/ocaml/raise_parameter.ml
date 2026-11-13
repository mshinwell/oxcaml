(* A function that raises its parameter, and one that catches whatever the first
   raises. Neither is called here. *)

external raise : exn -> 'a = "%raise"

let[@inline never] throw (e : exn) : int = raise e

let caught (e : exn) : int = try throw e with _ -> 0
