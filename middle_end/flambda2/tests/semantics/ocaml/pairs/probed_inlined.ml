(* Calls a function of another unit whose body has a probe, and lets Simplify
   inline it: the term after Simplify has the probe, and the unit is not
   checked. *)

external opaque : 'a -> 'a = "%opaque"

let two = Probed.bump (opaque 1)
