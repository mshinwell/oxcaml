(* Floating-point numbers passed around, with no arithmetic on them. Simplify
   inlines [choose] and takes the first. *)

external opaque : 'a -> 'a = "%opaque"

let[@inline] choose test (x : float) (y : float) = if test then x else y

let result = choose true 1.5 (opaque 2.5)
