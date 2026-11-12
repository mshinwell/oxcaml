(* The composition of two exported functions that are never inlined, by a
   function that is always inlined. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

let[@inline] compose f g x = f (g x)

let[@inline never] succ x = x + 1

let[@inline never] double x = x * 2

let succ_of_double x = compose succ double x
