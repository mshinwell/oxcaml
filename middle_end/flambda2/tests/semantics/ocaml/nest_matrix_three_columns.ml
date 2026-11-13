(* Three booleans with wildcards in each column: no column can be tested first
   without repeating a test. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] f a b c =
  match a, b, c with
  | _, false, true -> 1
  | false, true, _ -> 2
  | _, _, false -> 3
  | _, _, true -> 4

let result =
  f (opaque true) false true
  + (f false (opaque true) true * 10)
  + (f true true (opaque false) * 100)
  + (f (opaque true) true true * 1000)
  + (f false false (opaque false) * 10000)
