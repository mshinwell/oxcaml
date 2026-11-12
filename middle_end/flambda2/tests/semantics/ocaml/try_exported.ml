(* A function with a [try] that the unit exports. *)

external raise_notrace : exn -> 'a = "%raise_notrace"

let f x = try if x then raise_notrace Not_found else 1 with _ -> 2
