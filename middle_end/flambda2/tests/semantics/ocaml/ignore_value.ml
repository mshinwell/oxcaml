(* A value computed and ignored: its computation goes if it has no effect. *)

external ( * ) : int -> int -> int = "%mulint"

external ignore : 'a -> unit = "%ignore"

external opaque : 'a -> 'a = "%opaque"

let result =
  let x = opaque 6 in
  ignore (x * x, x);
  x
