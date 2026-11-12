(* Functions of the unit argument. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline] five () = 5

let[@inline] apply_to_unit f = f ()

let result = five () + apply_to_unit five
