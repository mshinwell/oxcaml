(* A call as the argument of a call: the extraction may move or share it. *)
let f a = Tick.consume (Tick.tick a) a
