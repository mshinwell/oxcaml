(* A call of a function that Simplify does not know: the call stays, and so does
   the function. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let result =
  let f = opaque (fun x -> x + 1) in
  f 3
