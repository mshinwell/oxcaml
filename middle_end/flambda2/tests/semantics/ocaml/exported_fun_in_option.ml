(* A function that returns an option of a function which needs nothing from
   around it. *)

external ( + ) : int -> int -> int = "%addint"

let wrapped () = Some (fun x -> x + 1)
