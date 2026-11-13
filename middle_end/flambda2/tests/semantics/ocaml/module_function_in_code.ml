(* A function of a module of the unit is called, from the code of another
   function, through the block of the module, which also holds a value that is
   computed when the unit runs. Simplify reads the field of the block that holds
   the function and calls it by its symbol. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

module Bounds = struct
  let floor = opaque 1

  let ceiling = 9

  let within x = if x < floor then floor else if ceiling < x then ceiling else x
end

let step x =
  let open Bounds in
  within (x + 2)

let result = step (opaque 0) + step 20
