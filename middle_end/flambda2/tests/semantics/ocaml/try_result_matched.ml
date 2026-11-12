(* A function that matches on the result of a [try]. *)

external raise : exn -> 'a = "%raise"

external ( < ) : int -> int -> bool = "%lessthan"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] positive x = if x < 0 then raise Not_found else x

let[@inline never] or_default x =
  match try Some (positive x) with _ -> None with
  | Some v -> v + 1
  | None -> 0

let result = or_default (opaque 5) + or_default (opaque (-5))
