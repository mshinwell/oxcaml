(* The first unit of a pair: a function that is never inlined, so that its code
   has no body in the .cmx of this unit. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline never] add_one x = x + 1
