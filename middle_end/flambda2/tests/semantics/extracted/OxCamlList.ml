open List

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let fold_left f init l = fold_left f l init
