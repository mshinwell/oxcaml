(* An exception that nothing catches: the unit raises. *)

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let result = if opaque true then raise Not_found else 1
