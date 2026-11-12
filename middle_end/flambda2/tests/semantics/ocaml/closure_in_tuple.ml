(* Two closures over the same variable, returned in a pair. Simplify inlines
   [make_pair], takes the pair apart and inlines both closures; [1 + base],
   which each of them computes, is computed once. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] make_pair base =
  (fun[@inline] x -> x + base), fun[@inline] x -> x + base + base

let result =
  let add_once, add_twice = make_pair (opaque 10) in
  add_once 1 + add_twice 1
