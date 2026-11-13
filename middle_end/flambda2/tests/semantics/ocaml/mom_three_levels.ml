(* Three matches, each on the result of the one inside it. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] f n =
  match
    match match n with 0 -> 1 | 1 -> 2 | _ -> 0 with
    | 1 -> 5
    | 2 -> 6
    | _ -> 7
  with
  | 5 -> 50
  | 6 -> 60
  | _ -> 70

let result = f (opaque 0) + (f (opaque 1) * 10) + (f (opaque 2) * 100)
