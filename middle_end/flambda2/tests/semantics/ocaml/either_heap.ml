(* A variant with two constructors that hold fields, built on both paths and
   matched after they meet. *)

external ( + ) : int -> int -> int = "%addint"

external on_heap : 'a -> 'a = "%identity"

type either =
  | Left of int
  | Right of int * int

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then Left (x + 1) else Right (x, x + 2) in
  match on_heap v with Left y -> y + 3 | Right (y, z) -> y + z

let result = f true 3 + f false 4
