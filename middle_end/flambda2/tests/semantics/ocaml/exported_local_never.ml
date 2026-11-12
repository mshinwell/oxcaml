(* A function with a function of its own inside, which is never inlined and
   needs nothing from around it. *)

external ( + ) : int -> int -> int = "%addint"

let f x =
  let[@inline never] step y = y + 1 in
  step (step x)
