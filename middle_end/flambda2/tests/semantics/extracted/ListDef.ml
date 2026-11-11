open Datatypes

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function [] -> [] | a :: l0 -> f a :: map f l0

(** val repeat : 'a1 -> nat -> 'a1 list **)

let rec repeat x = function O -> [] | S k -> x :: repeat x k
