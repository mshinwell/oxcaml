(* A recursive function on a list of options, whose patterns look at two
   elements at once. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let rec count_pairs l =
  match l with
  | Some x :: None :: rest -> x + count_pairs rest
  | Some x :: Some y :: rest -> (x * y) + count_pairs rest
  | None :: rest -> 1 + count_pairs rest
  | [Some x] -> 0 - x
  | [] -> 0

let result = count_pairs [Some 2; None; None; Some 3; Some (opaque 4); Some 5]
