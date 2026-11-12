(* [bind] on options, with a function that gives [None] on one of the two
   inputs. Simplify inlines everything and folds the whole to 4. *)

external ( + ) : int -> int -> int = "%addint"

external ( < ) : int -> int -> bool = "%lessthan"

type 'a option =
  | None
  | Some of 'a

let[@inline] bind option f = match option with None -> None | Some x -> f x

let[@inline] positive x = if 0 < x then Some x else None

let[@inline] value option = match option with None -> 0 | Some x -> x

let result =
  value (bind (positive 3) (fun x -> Some (x + 1)))
  + value (bind (positive (-3)) (fun x -> Some (x + 1)))
