open BinNums
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open OxCamlOption

type value =
  | Value_const of const
  | Value_closure of code_id * (value_slot * value) list
  | Value_symbol of symbol
  | Value_block of coq_Z * value list
  | Value_boxed_number of const

val kind_of_value : value -> flambda_kind

type statically_allocated_value =
  | Static_closure of code_id * (value_slot * value) list
  | Static_block of coq_Z * value list
  | Static_boxed_number of value
  | Static_string of coq_Z list

type static_env =
  { static_code : (code_id * code) list;
    static_values : (symbol * statically_allocated_value) list
  }

val empty_static_env : static_env

val closure_of :
  static_env -> value -> (code_id * (value_slot * value) list) option

val block_of : static_env -> value -> (coq_Z * value list) option

val boxable_number_of_const : const -> boxable_number option

val boxable_contents : const -> const option

val boxed_number_of : static_env -> value -> const option

val string_of : static_env -> value -> coq_Z list option

val is_allocated : static_env -> value -> bool
