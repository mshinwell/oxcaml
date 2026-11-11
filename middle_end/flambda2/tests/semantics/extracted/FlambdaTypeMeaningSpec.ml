open BinNums
open FlambdaModel
open FlambdaSemanticsSpec
open FlambdaTypeGrammar
open FlambdaValueSpec

(** val number_of_const : const -> coq_Z option **)

let number_of_const = function
  | Naked_immediate i -> Some i
  | Tagged_immediate i -> Some i
  | Naked_float32 i -> Some i
  | Naked_float i -> Some i
  | Naked_int8 i -> Some i
  | Naked_int16 i -> Some i
  | Naked_int32 i -> Some i
  | Naked_int64 i -> Some i
  | Naked_nativeint i -> Some i
  | Naked_vec128 i -> Some i
  | Naked_vec256 i -> Some i
  | Naked_vec512 i -> Some i
  | Naked_mask i -> Some i
  | _ -> None

(** val value_of_name : env -> name -> value option **)

let value_of_name vars n = eval_simple vars (simple_of_name n)

(** val closures_index_contents : (set_of_closures_contents, unit)
    row_like_index -> set_of_closures_contents **)

let closures_index_contents index =
  match index.index_domain with
  | Row_like_index_domain.Known contents -> contents
  | Row_like_index_domain.At_least contents -> contents
