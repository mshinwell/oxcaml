(* An optional argument with a default: omitted, given with its label, given as
   an option that is [None] and that is [Some], and given as an option that is
   not known when the unit is compiled. *)
external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

let scale ?(by = 10) x = x * by

let omitted = scale 3

let given = scale ~by:2 3

let given_none = scale ?by:None 3

let given_some = scale ?by:(Some 5) 3

let unknown_none = scale ?by:(opaque None) 3

let unknown_some = scale ?by:(opaque (Some 7)) 3
