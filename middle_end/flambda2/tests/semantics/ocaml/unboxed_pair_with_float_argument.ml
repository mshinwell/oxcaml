(* A function of an unboxed pair of an unboxed float and an integer, and of
   an integer, called directly: its code has three parameters, and the call
   is given their kinds. *)

external ( + ) : int -> int -> int = "%addint"

external box : float# -> float = "%box_float"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] f #((x : float#), (n : int)) (m : int) = box x, n + m

let result = f #(#1.5, opaque 3) 4
