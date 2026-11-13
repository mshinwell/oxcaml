(* Two loops, one in the other: the inner one has a pair for its accumulator,
   which the outer one makes at every turn and reads when the inner one is
   done. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external fst : 'a * 'b -> 'a = "%field0_immut"

external snd : 'a * 'b -> 'b = "%field1_immut"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let[@inline never] grid n =
  let total = ref 0 in
  for i = 1 to n do
    let acc = ref (i, 0) in
    for j = 1 to i do
      let a, b = !acc in
      acc := a + j, b + 1
    done;
    total := !total + fst !acc - snd !acc
  done;
  !total

let result = grid (opaque 4)
