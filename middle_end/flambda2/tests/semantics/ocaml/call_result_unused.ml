(* A recursive function that calls itself and does not use what the call
   returns. Simplify removes the parameter of the continuation that the call
   returns to. The call can then not return to it, and Simplify makes it return
   to a new continuation, bound at the call, under the [Let] of the argument;
   the old one, applied once, is inlined in it. The term before has the
   continuation of the call above that [Let]. *)

external ( - ) : int -> int -> int = "%subint"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

let rec count : int -> int -> int =
 fun n acc ->
  if n <= 0
  then acc
  else
    let _ = count (n - 1) acc in
    -1

let result = count 5 (opaque 4)
