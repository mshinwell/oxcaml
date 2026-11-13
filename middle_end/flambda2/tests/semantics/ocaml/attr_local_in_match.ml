(* A function marked [@local], used in three arms of a match. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type t =
  | A
  | B of int
  | C of int * int

let[@inline never] body v k =
  let[@local] finish a = (a * k) + 1 in
  match v with A -> finish 0 | B n -> finish n | C (m, n) -> finish (m + n)

let result = body A 3 + body (B (opaque 4)) 5 + body (C (2, opaque 6)) 7
