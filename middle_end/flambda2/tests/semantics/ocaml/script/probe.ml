(* A unit with a probe, which from_ocaml.sh refuses (probe.says): the text of
   its term does not say that the call of the handler is a probe. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] note (_ : int) = ()

let bump x =
  [%probe "bump" (note x)];
  x + 1

let result = bump (opaque 1)
