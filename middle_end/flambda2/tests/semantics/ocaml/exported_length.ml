(* The length of a list. *)

external ( + ) : int -> int -> int = "%addint"

let rec length l = match l with [] -> 0 | _ :: rest -> 1 + length rest
