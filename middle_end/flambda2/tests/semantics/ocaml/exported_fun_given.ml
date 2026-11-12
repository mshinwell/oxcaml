(* A function that gives a function which needs nothing from around it to the
   function it is given. *)

external ( + ) : int -> int -> int = "%addint"

let with_succ use = use (fun x -> x + 1)
