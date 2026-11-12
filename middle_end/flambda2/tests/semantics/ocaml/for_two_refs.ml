(* A [for] loop over two references. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 5 in
  let s = ref 0 in
  let p = ref 1 in
  for i = 1 to n do
    s := !s + i;
    p := !p * 2
  done;
  !s + !p
