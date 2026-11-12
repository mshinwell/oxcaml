(* A local function that captures a parameter of the function around it, called
   twice. Simplify inlines both functions and reads the captured variable. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] sum_of_two x =
  let[@inline] add y = x + y in
  add 1 + add 2

let result = sum_of_two (opaque 10)
