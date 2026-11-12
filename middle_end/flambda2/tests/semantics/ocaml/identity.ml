(* The polymorphic identity, applied to an integer and to itself. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] id x = x

let result = id (id (opaque 3)) + (id id) 4
