(* A functor applied twice to the same module. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

module type Num = sig
  val scale : int

  val shift : int -> int
end

module Make (N : Num) = struct
  let apply x = N.shift (x * N.scale)

  let twice x = apply (apply x)
end

module Arg = struct
  let scale = 4

  let shift x = x + 3
end

module One = Make (Arg)
module Two = Make (Arg)

let result = One.twice 1 + Two.twice (opaque 1) + One.apply (Two.apply 2)
