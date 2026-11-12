(* [map] on options, on [Some] and on [None]. Simplify inlines everything: no
   option is built. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type 'a option =
  | None
  | Some of 'a

let[@inline] map f option =
  match option with None -> None | Some x -> Some (f x)

let[@inline] value option ~default =
  match option with None -> default | Some x -> x

let result =
  value (map (fun x -> x + 1) (Some (opaque 4))) ~default:0
  + value (map (fun x -> x + 1) None) ~default:10
