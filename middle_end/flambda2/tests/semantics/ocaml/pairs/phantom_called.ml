(* Calls a function of another unit whose body, in the .cmx of that unit, has a
   phantom binding: a load of the first field of the argument, which the program
   does not run. The argument here has no field, and the program gives 0. The
   conversion refuses a phantom binding, so the body is left out of the
   prefix. *)

external opaque : 'a -> 'a = "%opaque"

external magic : 'a -> 'b = "%identity"

let r = Phantom.f (magic (opaque 0))
