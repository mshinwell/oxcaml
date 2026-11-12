(* A recursive function that returns what its recursive call returns, after work
   on it that comes to nothing: a record is made of it and the field read back.
   In the term before, once that work is gone, the call returns to a
   continuation whose handler only passes its parameter on to the return
   continuation of the function. Simplify makes the call return there. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( <= ) : int -> int -> bool = "%lessequal"

external opaque : 'a -> 'a = "%opaque"

type counted =
  { total : int;
    steps : int
  }

let rec sum_to : int -> int -> int =
 fun n acc ->
  if n <= 0
  then acc
  else
    let total = sum_to (n - 1) (acc + n) in
    { total; steps = n }.total

let result = sum_to (opaque 3) 0
