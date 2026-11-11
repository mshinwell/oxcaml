(* Closures with a captured variable. The two calls of [make_adder] are inlined,
   which leaves two closures whose value slot holds 5 and 7; the calls of those
   are made direct and inlined, and the projection of the slot becomes the
   constant. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] make_adder n = fun x -> x + n

let result =
  let add5 = make_adder 5 in
  let add7 = make_adder 7 in
  add5 (opaque 1) + add7 2
