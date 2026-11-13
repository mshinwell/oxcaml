(* A local reference that holds the total of a for loop. *)

external ( + ) : int -> int -> int = "%addint"

external ( * ) : int -> int -> int = "%mulint"

external ( = ) : int -> int -> bool = "%equal"

external opaque : 'a -> 'a = "%opaque"

type 'a ref = { mutable contents : 'a }

let[@inline never] body x =
  let local_ r = { contents = 0 } in
  for i = 1 to 10 do
    r.contents <- r.contents + (i * x)
  done;
  r.contents

let result = body (opaque 3) + body 10
