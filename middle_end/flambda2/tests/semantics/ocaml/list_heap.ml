(* A list that is built on both paths and matched after they meet. *)

external ( + ) : int -> int -> int = "%addint"

external on_heap : 'a -> 'a = "%identity"

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let l = if c then [x + 1] else [] in
  match on_heap l with [] -> x + 3 | y :: _ -> y + 2

let result = f true 3 + f false 4
