(* A function that calls a function of another unit. Before Simplify that is a
   load of a field of the module block of the other unit and a call of what is
   loaded, in code that the unit does not run. *)

external ( + ) : int -> int -> int = "%addint"

let length_plus_one l = Lengths.length l + 1
