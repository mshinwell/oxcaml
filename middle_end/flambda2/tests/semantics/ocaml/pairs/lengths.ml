(* The first unit of three pairs. [length_from] is recursive, so its code has no
   body in the .cmx of this unit; [length] is small and is inlined where it is
   called. *)

external ( + ) : int -> int -> int = "%addint"

type ints =
  | Nil
  | Cons of int * ints

let rec length_from n = function
  | Nil -> n
  | Cons (_, l) -> length_from (n + 1) l

let length l = length_from 0 l
