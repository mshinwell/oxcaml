(* A toplevel that reads the field of another unit of which the .cmx says what
   it holds. The module block of that unit also has a field of which the .cmx
   says nothing, which this unit does not read. *)

external ( + ) : int -> int -> int = "%addint"

let more = Hidden.known + 1
