(* A recursive function on lists, and a function that gives it a function which
   needs nothing from around it. *)

external ( + ) : int -> int -> int = "%addint"

let rec map f l = match l with [] -> [] | x :: rest -> f x :: map f rest

let incr_all l = map (fun x -> x + 1) l
