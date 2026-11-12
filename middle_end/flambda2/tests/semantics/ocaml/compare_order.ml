(* [compare] on two integers that are not known, and its result tested twice, in
   a function that is not inlined: Simplify makes each test a comparison of the
   two arguments, and the function no longer compares them three ways. *)

external compare : int -> int -> int = "%compare"

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] order a b =
  let c = compare a b in
  if c < 0 then 1 else if c > 0 then 2 else 0

let result =
  order (opaque 3) 4 + (10 * order (opaque 5) 5) + (100 * order (opaque 9) 2)
