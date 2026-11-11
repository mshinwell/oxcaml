(* A pair made by a function called when the module runs: the block that the
   call makes is a symbol once the call is inlined. *)

external opaque : 'a -> 'a = "%opaque"

let pair x y = x, y

let p = pair (opaque 1) 2
