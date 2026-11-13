(* A function of an unboxed float, called directly. The text of a term does
   not give the arity of the arguments of a direct call; the tool gives the
   call that of the parameters of its code. *)

external box : float# -> float = "%box_float"

external unbox : float -> float# = "%unbox_float"

let[@inline never] f (x : float#) = box x

let result = f (unbox 2.5), f #1.5
