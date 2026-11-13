(* A pattern that is the name of a type of tags, with an alias matched again at
   the smaller type. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type primary =
  [ `Red
  | `Green
  | `Blue ]

type extra =
  [ `Cyan
  | `Magenta of int ]

let[@inline never] f (c : [primary | extra]) =
  match c with
  | #primary as p -> ( match p with `Red -> 1 | `Green -> 2 | `Blue -> 3)
  | `Cyan -> 4
  | `Magenta n -> n

let result =
  f `Green
  + (f (opaque `Cyan) * 10)
  + (f (`Magenta (opaque 7)) * 100)
  + (f (opaque `Blue) * 1000)
