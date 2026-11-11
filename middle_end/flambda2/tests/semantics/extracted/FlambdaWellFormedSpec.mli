open BinNums
open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
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

val well_formed_unit : continuation -> expr -> bool
