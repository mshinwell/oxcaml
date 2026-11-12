(* A [try] whose body is a test of a value computed before it. *)

external raise_notrace : exn -> 'a = "%raise_notrace"

external opaque : 'a -> 'a = "%opaque"

let result =
  let c = opaque true in
  try if c then raise_notrace Not_found else 1 with _ -> 2
