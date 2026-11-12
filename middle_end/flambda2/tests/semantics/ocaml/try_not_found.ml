(* An exception raised and caught by name: the handler compares what was raised
   with the exception. *)

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let result =
  try if opaque true then raise Not_found else 1 with Not_found -> 2
