(* A recursive type, built three levels deep and read by functions that are not
   recursive. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type tree =
  | Leaf
  | Node of tree * int * tree

let[@inline] root tree =
  match tree with Leaf -> 100 | Node (_, value, _) -> value

let[@inline] left tree =
  match tree with Leaf -> Leaf | Node (left, _, _) -> left

let result =
  let tree = Node (Node (Leaf, opaque 1, Leaf), 2, Leaf) in
  root tree + root (left tree) + root (left (left tree))
