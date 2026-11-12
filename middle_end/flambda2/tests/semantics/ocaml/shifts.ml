(* The three shifts of integers. *)

external ( lsl ) : int -> int -> int = "%lslint"

external ( lsr ) : int -> int -> int = "%lsrint"

external ( asr ) : int -> int -> int = "%asrint"

external ( + ) : int -> int -> int = "%addint"

external opaque : 'a -> 'a = "%opaque"

let[@inline] pack high low = (high lsl 8) + low

let result = pack (opaque 3) 7 + (opaque (-16) asr 2) + (256 lsr 4)
