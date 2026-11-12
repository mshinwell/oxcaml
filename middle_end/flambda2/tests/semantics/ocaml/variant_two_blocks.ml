(* A match on a variant of two constant constructors and two constructors with
   arguments, where the constant constructors give their own numbers. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type t =
  | A
  | B
  | C of int
  | D of int * int

let[@inline never] f t =
  match t with A -> 0 | B -> 1 | C n -> n + 2 | D (n, _) -> n

let result = f (opaque B) + f (opaque (C 3))
