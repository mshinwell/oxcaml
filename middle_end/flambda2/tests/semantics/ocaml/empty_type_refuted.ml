(* A constructor whose argument is of a type with no value: a refutation case,
   and a match that has no case for it at all. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type empty = |

type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

let[@inline never] total (e : (int, empty) either) =
  match e with Left n -> n | Right _ -> .

let[@inline never] double (e : (int, empty) either) =
  match e with Left n -> n * 2

let result = total (Left (opaque 4)) + (double (Left (opaque 5)) * 10)
