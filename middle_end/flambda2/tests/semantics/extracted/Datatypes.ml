type nat =
  | O
  | S of nat

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function _, y -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m = match l with [] -> m | a :: l1 -> a :: app l1 m
