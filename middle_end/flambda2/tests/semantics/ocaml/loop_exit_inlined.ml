(* A function inlined where its argument is known: of the two branches of its
   test one is left, a loop. The continuation that follows the test is bound
   before the start of the loop is computed, and the loop leaves by a
   continuation of its own that applies it. Simplify, the other branch gone,
   puts the handler of the first in the second, which is bound at the loop,
   after that computation. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline] sum_or_zero b =
  let r =
    if b
    then (
      let acc = ref (opaque 9) in
      for i = 0 to 3 do
        acc := !acc + i
      done;
      !acc)
    else 0
  in
  r + opaque 1

let result = sum_or_zero true
