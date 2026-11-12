open BinNums
open BinPos
open List

(** val fresh_name : positive list -> positive **)

let fresh_name names = Pos.succ (fold_right Pos.max Coq_xH names)
