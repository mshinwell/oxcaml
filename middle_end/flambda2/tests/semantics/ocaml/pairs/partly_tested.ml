(* A function of this unit loads, from its argument, the field of which the .cmx
   of the first unit says nothing, and computes with it. The toplevel reads the
   field that the .cmx knows, and gives the function the record of the first
   unit. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline never] next (x : Partly.t) = x.hidden + 1

let known = Partly.r.known

let result = next Partly.r
