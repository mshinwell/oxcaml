(* A function that returns what a [try] gives, which the unit exports. It has a
   region, in which the closure given to the fold is allocated: the continuation
   that follows the [try] ends the region and passes its parameter on, and the
   body of the [try] applies it with the trap action that pops the handler. *)

external ( + ) : int -> int -> int = "%addint"

let rec fold_left f (acc : int) (l : int list) : int =
  match l with [] -> acc | x :: rest -> fold_left f (f acc x) rest

let sum_or_zero (g : int -> int) l =
  try fold_left (fun acc x -> acc + g x) 0 l with _ -> 0
