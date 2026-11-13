(* Two options, each made on the arms of its own test, matched together: the
   match tests the second option in each arm of its test of the first, and loads
   the contents of each in two arms. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline never] add_options c d x y =
  let a = if c then Some x else None in
  let b = if d then Some y else None in
  match a, b with
  | Some u, Some v -> u + v
  | Some u, None -> u
  | None, Some v -> v
  | None, None -> 0

let result =
  add_options (opaque true) (opaque true) 1 2
  + add_options (opaque true) (opaque false) 10 20
  + add_options (opaque false) (opaque true) 100 200
  + add_options (opaque false) (opaque false) 1000 2000
