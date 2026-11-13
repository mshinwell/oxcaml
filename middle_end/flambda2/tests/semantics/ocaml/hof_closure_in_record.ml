(* A closure kept in a field of a record, read and called. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type ops =
  { combine : int -> int -> int;
    unit_value : int
  }

let[@inline never] body x =
  let ops = { combine = (fun a b -> (a * x) + b); unit_value = x + 1 } in
  ops.combine (ops.combine ops.unit_value 2) 3

let result = body (opaque 3) + body 1
