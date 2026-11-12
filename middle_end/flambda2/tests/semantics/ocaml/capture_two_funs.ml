(* A function that returns a function of its own, which uses the argument and
   calls two functions of the module that are never inlined. The closure of the
   function returned holds the two in value slots; Simplify makes its code call
   their symbols. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline never] add a b = a + b

let[@inline never] twice a = a + a

let make n = fun x -> add (twice n) (twice x)
