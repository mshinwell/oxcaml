(* A function of an unboxed float, called through a value of which nothing is
   known. The text of a term does not give the arity of a call of unknown
   arity; the tool gives the call one kind for each argument. *)

external box : float# -> float = "%box_float"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] f (x : float#) = box x

let result = (opaque f) #1.5
