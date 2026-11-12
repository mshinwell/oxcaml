(* A function that returns a function which needs nothing from around it. *)

external ( + ) : int -> int -> int = "%addint"

let make () =
  let succ x = x + 1 in
  succ
