(* A record of a record built at a call; the function called copies it with the
   inner record changed, and another reads a field of the inner copy. Both are
   inlined. *)

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

let[@inline] width_of window = window.size.width

let[@inline] widen window =
  { window with size = { window.size with width = window.size.width + 1 } }

let[@inline never] widened_width title size = width_of (widen { title; size })

let result = widened_width 0 { width = opaque 3; height = 4 }
