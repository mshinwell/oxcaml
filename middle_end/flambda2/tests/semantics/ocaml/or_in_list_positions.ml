(* An or-pattern over lists of three shapes that binds an element at a different
   position in each. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] second_or_only l =
  match l with [x] | [_; x] | _ :: x :: _ :: _ -> x | [] -> 0

let result =
  second_or_only [opaque 5]
  + (second_or_only [1; opaque 6] * 10)
  + (second_or_only [1; opaque 7; 3; 4] * 100)
  + second_or_only []
