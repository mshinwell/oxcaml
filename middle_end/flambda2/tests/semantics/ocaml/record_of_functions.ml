(* A record that holds a function, called through the field. Simplify inlines
   [fold3] twice, reads the two fields and inlines the function each time. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type operations =
  { combine : int -> int -> int;
    start : int
  }

let[@inline] fold3 operations a b c =
  operations.combine
    (operations.combine (operations.combine operations.start a) b)
    c

let result =
  fold3 { combine = (fun[@inline] a b -> a + b); start = 10 } (opaque 1) 2 3
  + fold3 { combine = (fun[@inline] a b -> a * b); start = 2 } (opaque 2) 3 4
