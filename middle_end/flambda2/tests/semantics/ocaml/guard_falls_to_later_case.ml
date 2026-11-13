(* A guard that fails, with the next case of the same constructor after cases of
   other constructors. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external ( * ) : int -> int -> int = "%mulint"

external ( > ) : int -> int -> bool = "%greaterthan"

external opaque : 'a -> 'a = "%opaque"

type t =
  | A of int
  | B
  | C of int

let[@inline never] f v =
  match v with
  | A x when x > 0 -> x
  | B -> 100
  | C x when x > 0 -> x * 2
  | A _ -> 0 - 1
  | C _ -> 0 - 2

let result =
  f (A (opaque 5))
  + (f (A (opaque 0)) * 10)
  + f B
  + (f (C (opaque 3)) * 1000)
  + (f (C (opaque (-3))) * 10000)
