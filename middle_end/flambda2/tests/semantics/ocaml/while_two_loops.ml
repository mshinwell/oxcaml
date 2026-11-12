(* Two [while] loops, one after the other. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( < ) : int -> int -> bool = "%lessthan"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

external ref : 'a -> 'a ref = "%makemutable"

external ( ! ) : 'a ref -> 'a = "%field0"

external ( := ) : 'a ref -> 'a -> unit = "%setfield0"

let result =
  let n = opaque 4 in
  let a = ref 0 in
  let i = ref 0 in
  while !i < n do
    a := !a + !i;
    i := !i + 1
  done;
  let b = ref 1 in
  let j = ref 0 in
  while !j < n do
    b := !b * 2;
    j := !j + 1
  done;
  !a + !b
