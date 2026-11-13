(* A call of unknown arity that gives an argument of no kind, the unboxed
   product of nothing: from_ocaml.sh refuses it (void_argument.says). The
   compiler's call has two arguments and its code one parameter, so it is an
   over-application; the text does not write the second argument at all, and
   the call is read as a full application. *)

external opaque : 'a -> 'a = "%opaque"

let[@inline never] h (c : int) = fun #() -> c

let result = (opaque h) 5 #()
