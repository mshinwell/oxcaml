val sort_uniq : int list -> int list

val map_opt : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list option

val filter_map_opt : ('a1 -> 'a2 option option) -> 'a1 list -> 'a2 list option

val nth_int : 'a1 list -> int -> 'a1 option

val same_length : 'a1 list -> 'a2 list -> bool
