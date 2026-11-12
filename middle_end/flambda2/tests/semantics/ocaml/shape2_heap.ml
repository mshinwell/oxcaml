(* A variant with two constant constructors and one that holds two fields, built
   on three paths and matched after they meet; the constant constructors do not
   give their own number. *)

external ( + ) : int -> int -> int = "%addint"

external on_heap : 'a -> 'a = "%identity"

type shape =
  | Empty
  | Full
  | Pair of int * int

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then Pair (x + 1, x) else Full in
  match on_heap v with Empty -> 10 | Full -> x + 20 | Pair (a, b) -> a + b

let result = f true 3 + f false 4
