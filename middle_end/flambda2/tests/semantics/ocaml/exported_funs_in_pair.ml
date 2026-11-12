(* Two functions in a pair, and an exported function that calls the first. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external fst : 'a * 'b -> 'a = "%field0_immut"

let ops = (fun x -> x + 1), fun x -> x * 2

let apply_first x = (fst ops) x
