(* A toplevel that reads a field of another unit of which the .cmx says nothing,
   beside one that it knows. *)

external ( + ) : int -> int -> int = "%addint"

let sum = Hidden.known + Hidden.hidden
