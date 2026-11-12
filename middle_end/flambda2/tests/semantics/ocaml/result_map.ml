(* [map] on a result type. *)

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type ('a, 'b) result =
  | Ok of 'a
  | Error of 'b

let[@inline] map f r = match r with Ok x -> Ok (f x) | Error e -> Error e

let[@inline] ok_or r ~default = match r with Ok x -> x | Error _ -> default

let result = ok_or (map (fun x -> x * 2) (Ok (opaque 21))) ~default:0
