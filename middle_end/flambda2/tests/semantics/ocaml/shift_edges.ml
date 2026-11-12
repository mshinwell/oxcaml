(* Shifts at the edges of an OCaml integer, computed by Simplify. *)

external ( lsl ) : int -> int -> int = "%lslint"

external ( lsr ) : int -> int -> int = "%lsrint"

external ( asr ) : int -> int -> int = "%asrint"

let largest = -1 lsr 1

let least = 1 lsl 62

let top_bit_lost = 3 lsl 61

let sign_kept = -8 asr 1

let all_ones = -1 asr 62

let one = -1 lsr 62
