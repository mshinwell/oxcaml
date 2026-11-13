(* A functor applied to the result of a functor. *)

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

module Again (M : sig
  val apply : int -> int
end) =
struct
  let scale = M.apply 1

  let shift x = M.apply x
end

module Base = Make (struct
  let scale = 2

  let shift x = x + 1
end)

module Top = Make (Again (Base))

let result = Top.apply 3 + Top.twice (opaque 1)
