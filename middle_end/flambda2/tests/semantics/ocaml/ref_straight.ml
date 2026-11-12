(* A reference that does not escape, with no loop: the front end makes it a
   variable, and no block is made, read or written. *)

external ( + ) : int -> int -> int = "%addint"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

external opaque : 'a -> 'a = "%opaque"

let result =
  let r = ref (opaque 1) in
  r := !r + 1;
  r := !r + !r;
  !r
