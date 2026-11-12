(* A field of a field read twice, and another field of the same inner record. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type size =
  { width : int;
    height : int
  }

type window =
  { title : int;
    size : size
  }

let[@inline never] measure window =
  window.size.width + window.size.width + window.size.height + window.title

let result = measure { title = 1; size = { width = opaque 3; height = 4 } }
