(* Two handlers, one in the other; the inner one catches. *)

external raise : exn -> 'a = "%raise"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let result =
  try (try if opaque true then raise Not_found else 1 with _ -> 2) + 10
  with _ -> 0
