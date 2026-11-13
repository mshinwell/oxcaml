(* The dead arm divides by zero. *)

external ( + ) : int -> int -> int = "%addint"

external ( / ) : int -> int -> int = "%divint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

let[@inline] f flag x = if flag then x / 0 else x + 2

let result =
  (try f false (opaque 4) with Division_by_zero -> 1000)
  + try f true 4 with Division_by_zero -> 2000
