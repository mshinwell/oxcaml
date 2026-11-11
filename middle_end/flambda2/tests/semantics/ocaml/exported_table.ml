(* An exported function that reads a field of a constant of the module, the
   field being a function. The code of [first], which stays, projects the pair
   from its closure and loads the field; Simplify makes it return the symbol of
   [succ]. (A field that is a number shows nothing: the conversion from Lambda
   has already put the number in place of the load.) *)

external ( + ) : int -> int -> int = "%addint"

let succ x = x + 1

let table = succ, 20

let first () =
  let f, _ = table in
  f
