(* Labelled arguments given in another order than the parameters. *)

external ( - ) : int -> int -> int = "%subint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] subtract ~from ~amount = from - amount

let result = subtract ~amount:(opaque 3) ~from:10
