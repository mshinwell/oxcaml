(* [map] and [sum] written here, as there is no standard library. Simplify makes
   the closures symbols and leaves the calls. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

let rec map f list = match list with [] -> [] | x :: rest -> f x :: map f rest

let rec sum list = match list with [] -> 0 | x :: rest -> x + sum rest

let result = sum (map (fun x -> x * 2) [1; 2; 3])
