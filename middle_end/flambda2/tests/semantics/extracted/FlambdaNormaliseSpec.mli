open BinNums
open BinPos
open Datatypes
open FlambdaApplySpec
open FlambdaModel
open FlambdaNominalSpec
open FlambdaSemanticsSpec
open List
open ListDef
open PeanoNat

val name_in : positive -> positive list -> bool

val simple_in_scope : variable list -> simple -> bool

val simples_in_scope : variable list -> simple list -> bool

val named_in_scope : variable list -> named -> bool

val static_binding_in_scope : variable list -> static_binding -> bool

val apply_cont_in_scope :
  variable list -> continuation list -> apply_cont -> bool

val expr_in_scope : variable list -> continuation list -> expr -> bool

val handler_in_scope :
  variable list -> continuation list -> continuation_handler -> bool

val inline_renaming :
  continuation -> continuation -> continuation -> continuation -> renaming

val var_in_simples : variable -> simple list -> bool

val inlinable_b : apply_expr -> code -> bool

val codes_of :
  static_binding list -> (code_id * code) list -> (code_id * code) list

val inline_apply : (code_id * code) list -> apply_expr -> expr

val inline_calls : (code_id * code) list -> expr -> expr

val var_in_simple : variable -> simple -> bool

val var_in_value_slots : variable -> (value_slot * simple) list -> bool

val var_in_named : variable -> named -> bool

val var_in_static_binding : variable -> static_binding -> bool

val var_free_b : variable -> expr -> bool

val var_free_in_handler_b : variable -> continuation_handler -> bool

val remove_unused_lets : expr -> expr

val remove_unused_lets_in_handler : continuation_handler -> continuation_handler
