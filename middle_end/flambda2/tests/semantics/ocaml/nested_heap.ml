(* An option of a pair, built on both paths and matched after they meet. *)

external ( + ) : int -> int -> int = "%addint"

external on_heap : 'a -> 'a = "%identity"

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then Some (x + 1, x) else None in
  match on_heap v with None -> 0 | Some (a, b) -> a + b

let result = f true 3 + f false 4
