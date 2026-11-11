open Datatypes

val nth_error : 'a1 list -> nat -> 'a1 option

val list_eq_dec : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list
