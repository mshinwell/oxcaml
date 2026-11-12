(* An exception caught and raised again, in another handler. *)

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let result =
  try try if opaque true then raise Not_found else 1 with e -> raise e
  with _ -> 3
