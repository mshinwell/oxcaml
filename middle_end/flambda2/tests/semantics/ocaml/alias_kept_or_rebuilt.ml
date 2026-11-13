(* The value matched returned by its alias, and the same value built again from
   what the pattern bound. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] keep o = match o with Some _ as same -> same | None -> None

let[@inline never] rebuild o = match o with Some x -> Some x | None -> None

let value = opaque (Some 7)

let result =
  (match keep value with Some x -> x | None -> 0)
  + match rebuild value with Some x -> x * 10 | None -> 0
