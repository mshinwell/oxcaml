(* A function that returns a closure, inlined, and the closure called at once:
   [make] is given one argument and called with three. Once [make] is inlined,
   the closure that it returns is bound by a [Let] and called with one argument
   more than its code takes. Simplify inlines the full call and applies what it
   returns to the argument that remains. The validation makes the call direct
   and splits it into the full call and the call of its result
   (FlambdaNormaliseSpec.split_over_application). *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] make n =
  let add x = x + n in
  let get () = add in
  get

let result = make (opaque 3) () 4
