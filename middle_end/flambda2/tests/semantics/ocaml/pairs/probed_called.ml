(* Calls a function of another unit whose body has a probe, and forbids its
   inlining. The body is in the .cmx of that unit; the conversion refuses a call
   that is a probe, so the body is left out of the prefix. *)

external opaque : 'a -> 'a = "%opaque"

let two = (Probed.bump [@inlined never]) (opaque 1)
