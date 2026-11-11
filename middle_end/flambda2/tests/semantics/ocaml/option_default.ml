(* An option built and matched at once: the [Some] block is made, tested and
   read; Simplify leaves the addition. (For the type annotation, see
   [match_variant.ml].) *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] value_or : int -> int option -> int =
 fun default o -> match o with None -> default | Some x -> x

let result = value_or 0 (Some (opaque 3)) + value_or 7 None
