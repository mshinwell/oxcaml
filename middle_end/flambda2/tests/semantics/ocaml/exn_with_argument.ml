(* An exception with an argument, raised and caught by name: the handler reads
   the argument. *)

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

external length : string -> int = "%string_length"

let result =
  try if opaque true then raise (Invalid_argument "four") else 1
  with Invalid_argument s -> length s
