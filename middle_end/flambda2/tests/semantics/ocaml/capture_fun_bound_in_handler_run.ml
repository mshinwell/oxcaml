(* As capture_fun_and_var_run.ml, with a function of the module that uses a
   value chosen by a test when the module runs. The closure of that function
   holds the value, so its symbol is bound in the handler of the test; the code
   of the function returned is bound at the head of the unit, and reads the
   function from a value slot. Simplify makes that code call the symbol. The
   validation does too, once it has no more to lift: it then reads a known value
   slot with every symbol that the unit binds taken to be in scope
   (FlambdaKnownSlotsSpec.read_known_slots_anywhere). Validated. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let base = if opaque true then 1 else 2

let[@inline never] add a b = a + b + base

let[@inline never] make n = fun x -> add n x

let result = (make (opaque 1)) 2
