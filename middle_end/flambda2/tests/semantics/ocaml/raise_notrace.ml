(* An exception raised with no backtrace. *)

external raise_notrace : exn -> 'a = "%raise_notrace"

external opaque : 'a -> 'a = "%opaque"

let result =
  try if opaque true then raise_notrace Not_found else 1 with _ -> 2
