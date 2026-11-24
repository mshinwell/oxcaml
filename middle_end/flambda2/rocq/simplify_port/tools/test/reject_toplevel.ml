(* A computation as a top-level value: run once when the module starts, not
   at each use. *)
let v = Tick.tick 0
