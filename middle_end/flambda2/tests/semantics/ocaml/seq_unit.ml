(* Sequences and the unit value. *)

external opaque : 'a -> 'a = "%opaque"

external ignore : 'a -> unit = "%ignore"

let[@inline] discard x = ignore x

let result =
  discard (opaque 1);
  ();
  3
