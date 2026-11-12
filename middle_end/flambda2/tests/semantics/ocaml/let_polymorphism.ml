(* A function used at two types. It takes a pair, and both calls give it one
   written out, so they are direct calls with the components as arguments. *)

external ( + ) : int -> int -> int = "%addint"

let[@inline] first (a, _) = a

let result =
  let pair = first (1, true), first ("one", 2) in
  match pair with n, _ -> n + 1
