(* A list whose head is not known until the module runs. *)

external opaque : 'a -> 'a = "%opaque"

let l = [opaque 1; 2; 3]
