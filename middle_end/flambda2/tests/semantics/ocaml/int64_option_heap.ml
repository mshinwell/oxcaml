(* An option of a boxed 64-bit integer that is built on both paths and matched
   after they meet. *)

external add : int64 -> int64 -> int64 = "%int64_add"

external to_int : int64 -> int = "%int64_to_int"

external on_heap : 'a -> 'a = "%identity"

let[@inline never] f : bool -> int64 -> int64 =
 fun c x ->
  let v = if c then Some (add x 1L) else None in
  match on_heap v with None -> 0L | Some y -> add y 2L

let result = to_int (add (f true 3L) (f false 4L))
