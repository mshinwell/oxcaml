(* A record of two functions, and a function that calls one of them. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

type ops =
  { incr : int -> int;
    decr : int -> int
  }

let ops = { incr = (fun x -> x + 1); decr = (fun x -> x - 1) }

let up x = ops.incr x
