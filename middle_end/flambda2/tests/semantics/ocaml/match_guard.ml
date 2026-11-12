(* A match with a guard, at three known options. *)

external ( + ) : int -> int -> int = "%addint"

external ( > ) : int -> int -> bool = "%greaterthan"

type 'a option =
  | None
  | Some of 'a

let[@inline] positive_or_zero option =
  match option with Some x when x > 0 -> x | Some _ -> 0 | None -> 0

let result =
  positive_or_zero (Some 5)
  + positive_or_zero (Some (-5))
  + positive_or_zero None
