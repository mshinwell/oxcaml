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

val well_formed_unit : continuation -> expr -> bool
