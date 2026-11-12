(* A recursive function over a list, exported and not called. *)

external ( + ) : int -> int -> int = "%addint"

let rec length l = match l with [] -> 0 | _ :: t -> 1 + length t
