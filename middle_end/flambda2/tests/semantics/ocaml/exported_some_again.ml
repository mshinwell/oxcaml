(* A value that is not known until the module runs, put in an option and taken
   out again by a function that is inlined, and then kept in another option. *)

external opaque : 'a -> 'a = "%opaque"

let[@inline] get o = match o with Some x -> x | None -> 0

let v = opaque 6

let inside = get (Some v)

let kept = Some inside
