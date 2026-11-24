(* A computation bound by a plain let and run twice: in Rocq two runs, in
   direct style one. *)
let f a =
  let x = Tick.tick a in
  port__bind x (fun y -> port__bind x (fun z -> port__ret (y, z)))
