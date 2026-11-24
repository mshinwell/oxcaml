(* The tidying keeps the effects and their order: an effect bound to the
   name [fuel] stays; of two effects that go to two fields of a record only
   one goes into the record; the read of a field is not crossed; a handler
   of a constant exception that names its argument gets it. *)
let f a = port__bind (Tick.tick a) (fun fuel -> port__ret ())

let g () =
  port__bind (Tick.tick 1) (fun tmp1 ->
    port__bind (Tick.tick 2) (fun tmp2 ->
      port__ret { Rec.left = tmp1; right = tmp2 }))

let h r =
  port__bind (Tick.set r 1) (fun tmp1 -> port__ret (tmp1, r.Rec.contents))

let k () =
  port__try_with (fun _ -> port__raise Not_found ()) Not_found (fun u ->
    port__ret u)
