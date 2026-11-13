(* The unit of probe.ml with a plain call where that one has a probe:
   from_ocaml.sh makes its text (probe_not.says). *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] note (_ : int) = ()

let bump x =
  note x;
  x + 1

let result = bump (opaque 1)
