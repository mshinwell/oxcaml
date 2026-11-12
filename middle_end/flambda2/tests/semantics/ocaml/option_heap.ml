(* An option that is built on both paths and matched after they meet. The
   identity takes its argument on the heap, so that the option is not allocated
   in a region. *)

external ( + ) : int -> int -> int = "%addint"

external on_heap : 'a -> 'a = "%identity"

let[@inline never] f : bool -> int -> int =
 fun c x ->
  let v = if c then Some (x + 1) else None in
  match on_heap v with None -> 0 | Some y -> y + 2

let result = f true 3 + f false 4
