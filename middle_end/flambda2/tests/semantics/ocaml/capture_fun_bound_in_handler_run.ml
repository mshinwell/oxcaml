(* As capture_fun_and_var_run.ml, with a function of the module that uses a
   value chosen by a test when the module runs. The closure of that function
   holds the value, so its symbol is bound in the handler of the test; the code
   of the function returned is bound at the head of the unit, and reads the
   function from a value slot. Simplify makes that code call the symbol. The
   validation does not: it puts a symbol in the place of a value slot only where
   the symbol is in scope (FlambdaKnownSlotsSpec.v), and this one is bound below
   the code. Not validated. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let base = if opaque true then 1 else 2

let[@inline never] add a b = a + b + base

let[@inline never] make n = fun x -> add n x

let result = (make (opaque 1)) 2
