(* A match of four constants with no array in the source: the only array of the
   term after is the table. gives: s = 181 | w = 270 *)

type dir =
  | North
  | East
  | South
  | West

let[@inline never] [@local never] degrees (d : dir) =
  match d with North -> 5 | East -> 90 | South -> 181 | West -> 270

let s : int = degrees (Sys.opaque_identity South)

let w : int = degrees West
