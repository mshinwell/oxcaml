(* The first of two units given to the driver in one process. It asks for the
   classic mode, so the compiler does not run Simplify on it. *)

[@@@ocaml.flambda_oclassic]

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let result = opaque 1 + 2
