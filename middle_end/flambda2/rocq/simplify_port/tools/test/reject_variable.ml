(* A parameter that is a computation, run by the function. *)
let f m = port__bind m (fun y -> port__ret y)
