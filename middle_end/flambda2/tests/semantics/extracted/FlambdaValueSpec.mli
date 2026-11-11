open BinNums
open BinPos
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open OxCamlOption

type location = positive

type value =
  | Value_const of const
  | Value_closure of code_id * (value_slot * value) list
  | Value_closure_of_set of
      function_slot * (function_slot * code_id) list * (value_slot * value) list
  | Value_symbol of symbol
  | Value_block of coq_Z * value list
  | Value_boxed_number of const
  | Value_location of location

val kind_of_value : value -> flambda_kind

type statically_allocated_value =
  | Static_closure of code_id * (value_slot * value) list
  | Static_closure_of_set of
      function_slot
      * (function_slot * symbol) list
      * (function_slot * code_id) list
      * (value_slot * value) list
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

val unnamed_function_slot : function_slot

val closure_in_set :
  static_env ->
  value ->
  ((function_slot * (function_slot * code_id) list) * (value_slot * value) list)
  option

val project_value_slot :
  static_env -> function_slot -> value_slot -> value -> value option

val project_function_slot :
  static_env -> function_slot -> function_slot -> value -> value option

val block_of : static_env -> value -> (coq_Z * value list) option

val boxable_number_of_const : const -> boxable_number option

val boxable_contents : const -> const option

val boxed_number_of : static_env -> value -> const option

val string_of : static_env -> value -> coq_Z list option

val is_allocated : static_env -> value -> bool
