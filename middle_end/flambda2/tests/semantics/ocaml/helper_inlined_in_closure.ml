(* A function that the unit does not export, called by a function that is never
   inlined and that also uses a value of the unit that is not known. The closure
   of the second holds the first in a value slot. Simplify inlines the call in
   the code of the second and removes the slot, the closure of the first and its
   code. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let n = opaque 1

let double y = y * 2

let[@inline never] g x = double (x + n)

let result = g 2 + g 7
