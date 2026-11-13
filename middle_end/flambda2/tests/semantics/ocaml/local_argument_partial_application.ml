(* A function whose first parameter is local, given a pair that lives on the
   stack of the caller: the partial application is local too, and is applied
   twice before the caller returns. *)
external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] pick (local_ p : int * int) (first : bool) : int =
  let a, b = p in
  if first then a else b

let[@inline never] both (x : int) (y : int) : int =
  let local_ p = x, y in
  let choose = pick p in
  let a = choose true in
  let b = choose false in
  (a * 10) + b

let result = both (opaque 3) (opaque 4)

let result_again = both 5 6
