(* A function from one type of constant constructors to another is inlined into
   a match on its result. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type color =
  | Red
  | Green
  | Blue

type light =
  | Stop
  | Go
  | Wait

let[@inline] to_light c =
  match c with Red -> Stop | Green -> Go | Blue -> Wait

let[@inline never] delay c =
  match to_light c with Stop -> 30 | Go -> 0 | Wait -> 5

let result =
  delay (opaque Red)
  + (delay (opaque Green) * 100)
  + (delay (opaque Blue) * 1000)
