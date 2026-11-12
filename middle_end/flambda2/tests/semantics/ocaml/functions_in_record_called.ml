(* Two functions of the unit kept in an exported record and called through its
   fields. *)

external ( + ) : int -> int -> int = "%addint"

external ( - ) : int -> int -> int = "%subint"

external opaque : 'a -> 'a = "%opaque"

type ops =
  { apply : int -> int;
    undo : int -> int
  }

let[@inline never] up x = x + 1

let[@inline never] down x = x - 1

let ops = { apply = up; undo = down }

let result = ops.undo (ops.apply (opaque 5))
