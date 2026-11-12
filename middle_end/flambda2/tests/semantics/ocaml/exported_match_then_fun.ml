(* A value taken out of an option that is not known until the module runs,
   and then a predicate that uses it. *)

external gt : int -> int -> bool = "%gtint"

external opaque : 'a -> 'a = "%opaque"

let limit = match opaque (Some 3) with Some n -> n | None -> 0

let above x = gt x limit
