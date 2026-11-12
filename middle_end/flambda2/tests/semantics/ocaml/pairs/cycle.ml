(* The first unit of a pair: two blocks that name each other. The compiler makes
   them by calls of C functions of the runtime, which the model has not got, so
   this unit is not checked; and its .cmx says nothing of the two fields. *)

type ints =
  | Nil
  | Cons of int * ints

let rec ones = Cons (1, twos)

and twos = Cons (2, ones)
