(* An immutable array made and read in a function that is not inlined,
   at an index that is an argument. Simplify leaves the array and the
   load where they are. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

external get : 'a iarray -> int -> 'a = "%array_unsafe_get"

let[@inline never] pick a b i = get [: a; b; a + b :] i

let result = pick (opaque 2) (opaque 5) (opaque 2)
