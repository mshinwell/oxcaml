(* The first unit of a pair: a function that is inlined wherever it may be, and
   whose body has a probe. This unit has no expected file: the text of its term
   does not say that a call is a probe, so a verdict of the tool on it would be
   of a term that is not the compiler's. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline never] note (_ : int) = ()

let[@inline] bump x =
  [%probe "bump" (note x)];
  x + 1
