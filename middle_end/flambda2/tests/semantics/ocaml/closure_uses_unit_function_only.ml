(* A function that returns a closure, which calls another function of the unit
   and captures nothing else. Neither function is inlined. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] double x = x * 2

let[@inline never] doubler () = fun x -> double (x + 1)

let result =
  let f = doubler () in
  let g = doubler () in
  f (opaque 2) + g 4
