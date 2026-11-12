(* An exception raised and caught by a handler that catches everything. *)

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let result = try if opaque true then raise Not_found else 1 with _ -> 2
