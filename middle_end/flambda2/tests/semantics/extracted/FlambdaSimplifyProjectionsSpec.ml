open BinNums
open FlambdaTypeGrammar

(** val make_block_type : coq_Z -> flambda_type list -> flambda_type **)

let make_block_type tag tys =
  immutable_block false tag (Scannable Value_only) Alloc_mode.Heap tys
