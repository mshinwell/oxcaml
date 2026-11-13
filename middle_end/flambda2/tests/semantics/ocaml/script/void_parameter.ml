(* A partial application, by a call of unknown arity, of a function whose
   second parameter has no kind: from_ocaml.sh refuses it
   (void_parameter.says). The text writes one parameter for the code, and the
   call, which has one argument, is read as a full application: the unit read
   has 5 where the program has a closure. *)

external opaque : 'a -> 'a = "%opaque"

let[@inline never] h (c : int) #() = c

let p = (opaque h) 5
