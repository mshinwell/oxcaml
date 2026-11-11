open BinNums
open BinPos
open Datatypes
open FlambdaBindersSpec
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveSpec
open List
open ListDef

val free_continuations : expr -> continuation list

val handler_free_continuations : continuation_handler -> continuation list

val raises_to : continuation -> expr -> bool

val handler_raises_to : continuation -> continuation_handler -> bool

val handler_at_toplevel : continuation -> continuation -> expr -> bool

val statics_at_toplevel : continuation -> bool -> expr -> bool

val handler_statics_at_toplevel :
  continuation -> bool -> continuation_handler -> bool

val binding_statics_at_toplevel : continuation -> static_binding -> bool

val code_statics_at_toplevel : continuation -> code -> bool

val code_ids_of_binding : static_binding -> code_id list

val symbols_of_binding : static_binding -> symbol list

val static_names : (static_binding -> positive list) -> expr -> positive list

val handler_static_names :
  (static_binding -> positive list) -> continuation_handler -> positive list

val set_well_formed : function_slot -> (function_slot * code_id) list -> bool

val named_sets_well_formed : named -> bool

val binds_symbol_to : symbol -> static_const -> static_binding -> bool

val static_set_whole : static_binding list -> static_binding -> bool

val static_set_code_ids : static_binding -> code_id list

val binds_symbol_of_set : static_binding -> static_binding -> bool

val static_sets_code_disjoint : static_binding list -> bool

val sets_well_formed : expr -> bool

val handler_sets_well_formed : continuation_handler -> bool

val binding_sets_well_formed : static_binding -> bool

val code_sets_well_formed : code -> bool

val simple_in_range : simple -> bool

val value_slots_in_range : (value_slot * simple) list -> bool

val named_in_range : named -> bool

val static_const_in_range : static_const -> bool

val apply_cont_in_range : apply_cont -> bool

val apply_in_range : apply_expr -> bool

val arm_in_range : coq_Z * apply_cont -> bool

val numbers_in_range : expr -> bool

val handler_numbers_in_range : continuation_handler -> bool

val binding_numbers_in_range : static_binding -> bool

val code_numbers_in_range : code -> bool

type unit_interface =
  { unit_return : continuation;
    unit_exn : continuation
  }

val well_formed_unit : unit_interface -> expr -> bool
