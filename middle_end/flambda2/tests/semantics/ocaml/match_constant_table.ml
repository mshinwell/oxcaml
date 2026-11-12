(* An exhaustive match from seven constant constructors to seven integers that
   follow no rule: it can be made a table of constants. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type day =
  | Mon
  | Tue
  | Wed
  | Thu
  | Fri
  | Sat
  | Sun

let[@inline never] hours d =
  match d with
  | Mon -> 8
  | Tue -> 6
  | Wed -> 9
  | Thu -> 7
  | Fri -> 4
  | Sat -> 0
  | Sun -> 1

let result = hours (opaque Wed) + hours (opaque Fri) + hours (opaque Sun)
