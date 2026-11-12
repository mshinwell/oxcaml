(* [land] and [=] at constants, through an inlined function. *)

external ( land ) : int -> int -> int = "%andint"

external ( = ) : int -> int -> bool = "%equal"

external ( && ) : bool -> bool -> bool = "%sequand"

external not : bool -> bool = "%boolnot"

let[@inline] is_even x = x land 1 = 0

let result = is_even 10 && not (is_even 7)
