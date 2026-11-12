(* A raise to a handler that also catches the exceptions of a call and looks at
   none of them. Simplify knows what the call returns and removes it, so the
   handler is an ordinary continuation and the raise a jump with no argument. *)

external raise : exn -> 'a = "%raise"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] f x = x

let result = try if opaque true then raise Not_found else f 1 with _ -> 2
