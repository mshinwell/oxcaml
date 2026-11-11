open BinInt
open BinNums
open BinPos
open Datatypes
open FlambdaModel
open List
open ListDef

type value =
  | Value_const of const
  | Value_closure of code_id * (value_slot * value) list
  | Value_symbol of symbol

val eval_prim : prim -> value list -> value option

val lookup : positive -> (positive * 'a1) list -> 'a1 option

type env = (variable * value) list

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

type cont_value =
  | Closure of
      continuation_handler
      * env
      * (continuation * cont_value) list
      * (continuation * continuation_handler) list
  | Outer of continuation

type cont_env = (continuation * cont_value) list

val resolve : continuation -> cont_env -> cont_value

val rec_closures :
  (continuation * continuation_handler) list -> env -> cont_env -> cont_env

val eval_simple : env -> simple -> value option

val eval_simples : env -> simple list -> value list option

val eval_value_slots :
  env -> (value_slot * simple) list -> (value_slot * value) list option

val closure_of :
  static_env -> value -> (code_id * (value_slot * value) list) option

val eval_named : static_env -> env -> named -> value option

val eval_static_const : env -> static_const -> statically_allocated_value option

val eval_static_bindings :
  env -> static_binding list -> static_env -> static_env option

val binding_binds : static_binding -> bool

val binds_statics : expr -> bool

val handler_binds_statics : continuation_handler -> bool

val handlers_bind_statics : (continuation * continuation_handler) list -> bool

val bind_params : variable list -> value list -> env -> env option

val find_arm : coq_Z -> (coq_Z * apply_cont) list -> apply_cont option

val naked_immediate_of_value : value -> coq_Z option

type state =
  { state_expr : expr;
    state_vars : env;
    state_conts : cont_env;
    state_statics : static_env
  }

type step_result =
  | Step of state
  | Exit of continuation * value list
  | Undefined

val apply_cont_value : cont_value -> value list -> static_env -> step_result

val apply_continuation :
  continuation -> value list -> cont_env -> static_env -> step_result

val call_function :
  value ->
  call_kind ->
  value list ->
  cont_value ->
  cont_value ->
  static_env ->
  step_result

val step : state -> step_result

val run : nat -> state -> step_result
