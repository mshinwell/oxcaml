(* An option that is built on both paths and matched after they meet. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then Some (x + 1) else None in
  match v with None -> 0 | Some y -> y + 2

let result = f true 3 + f false 4
