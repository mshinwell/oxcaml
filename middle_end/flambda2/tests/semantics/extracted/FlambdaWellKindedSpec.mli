open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveSpec
open FlambdaSemanticsSpec
open FlambdaValueSpec
open List
open ListDef
open OxCamlOption
open PeanoNat

type kind_env = flambda_kind finite_map

type arity_env = flambda_kind list finite_map

type slot_kinds = flambda_kind finite_map

val has_kind : flambda_kind option -> flambda_kind -> bool

val has_arity : flambda_kind list option -> flambda_kind list -> bool

val kind_of_simple : kind_env -> simple -> flambda_kind option

val kinds_of_simples : kind_env -> simple list -> flambda_kind list option

val bind_param_kinds :
  variable list -> flambda_kind list -> kind_env -> kind_env option

val handler_arities : (continuation * continuation_handler) list -> arity_env

val value_slots_well_kinded :
  slot_kinds -> kind_env -> (value_slot * simple) list -> bool

val kind_of_named : slot_kinds -> kind_env -> named -> flambda_kind option

val static_const_well_kinded : slot_kinds -> kind_env -> static_const -> bool

val apply_cont_well_kinded : kind_env -> arity_env -> apply_cont -> bool

val apply_well_kinded : kind_env -> arity_env -> apply_expr -> bool

val well_kinded : slot_kinds -> kind_env -> arity_env -> expr -> bool

val unit_arities : continuation -> continuation -> arity_env

val well_kinded_unit :
  slot_kinds -> continuation -> continuation -> expr -> bool

val kinds_agree_on_prefix :
  flambda_kind list list -> flambda_kind list list -> bool

val is_one_param_of_kind_value : arity -> bool

val partial_or_over_application : arity -> arity -> arity -> arity -> bool

val at_partial_or_over_application : state -> bool
