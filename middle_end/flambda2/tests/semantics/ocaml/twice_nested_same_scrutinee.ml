(* A match on a value inside a case of a match on the same value: the inner one
   has a case that cannot be taken. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] f o =
  match o with
  | Some x -> ( match o with Some y -> x + y | None -> 1000)
  | None -> ( match o with Some _ -> 2000 | None -> 3)

let result = f (Some (opaque 21)) + (f (opaque None) * 100)
