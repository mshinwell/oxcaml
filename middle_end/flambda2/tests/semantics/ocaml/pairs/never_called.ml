(* Calls of a function of another unit whose code has no body in the .cmx: one
   in a function, one at toplevel. *)

let add_two x = Never.add_one (Never.add_one x)

let two = Never.add_one 1
