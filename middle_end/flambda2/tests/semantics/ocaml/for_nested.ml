(* A [for] loop in a [for] loop, the bound of the inner one being the index of
   the outer one. *)

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 3 in
  let s = ref 0 in
  for i = 1 to n do
    for j = 1 to i do
      s := !s + j
    done
  done;
  !s
