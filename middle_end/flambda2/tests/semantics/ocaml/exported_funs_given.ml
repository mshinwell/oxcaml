(* A function that gives two functions which need nothing from around them to
   the function it is given. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

let with_both use = use (fun x -> x + 1) (fun x -> x - 1)
