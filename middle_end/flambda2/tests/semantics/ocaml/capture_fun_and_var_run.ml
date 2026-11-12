(* A function, never inlined, that returns a function of its own which uses the
   argument and calls a function of the module that is never inlined; the
   function returned is called. The closure of the function returned holds the
   function of the module in a value slot, and its code reads the slot to call
   it; Simplify, which knows what the slot holds, makes that code call the
   symbol of the function. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] add a b = a + b

let[@inline never] make n = fun x -> add n x

let result = (make (opaque 1)) 2
