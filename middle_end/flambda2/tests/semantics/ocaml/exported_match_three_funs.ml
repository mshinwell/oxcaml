(* A function chosen by a match of three cases when the module runs. *)

external opaque : 'a -> 'a = "%opaque"

external ( + ) : int -> int -> int = "%addint"

let g =
  match opaque 1 with
  | 0 -> fun x -> x
  | 1 -> fun x -> x + 1
  | _ -> fun x -> x + 2
