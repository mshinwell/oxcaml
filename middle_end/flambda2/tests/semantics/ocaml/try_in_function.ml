(* A function with a [try] that is inlined where it is called. *)

external raise_notrace : exn -> 'a = "%raise_notrace"

external opaque : 'a -> 'a = "%opaque"

let[@inline] f x = try if x then raise_notrace Not_found else 1 with _ -> 2

let result = f (opaque true)
