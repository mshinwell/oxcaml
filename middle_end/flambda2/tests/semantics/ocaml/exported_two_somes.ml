(* Two options, each of a value that is not known until the module runs. *)

external opaque : 'a -> 'a = "%opaque"

let a = Some (opaque 1)

let b = Some (opaque 2)
