open BinPos
open Datatypes
open FlambdaMapSpec
open FlambdaModel
open List
open ListDef

val free_variables_of_simple : simple -> variable list

val free_variables_of_simples : simple list -> variable list

val free_variables_of_value_slots : (value_slot * simple) list -> variable list

val free_variables_of_named : named -> variable list

val free_variables_of_static_const : static_const -> variable list

val free_variables_of_apply_cont : apply_cont -> variable list

val free_variables_of_apply : apply_expr -> variable list

val free_variables_of_expr : expr -> variable list

val free_variables_of_handler : continuation_handler -> variable list

val free_variables_of_binding : static_binding -> variable list

val free_variables_of_code : code -> variable list

val free_continuations_of_expr : expr -> continuation list

val free_continuations_of_handler : continuation_handler -> continuation list

val free_continuations_of_binding : static_binding -> continuation list

val free_continuations_of_code : code -> continuation list

val names_among : variable list -> continuation list -> expr -> bool

val names_in_scope : continuation -> continuation -> expr -> bool

val binders_distinct : expr -> bool

val handler_binders_distinct : continuation_handler -> bool

val binding_binders_distinct : static_binding -> bool

val code_binders_distinct : code -> bool

val code_closed : expr -> bool

val handler_code_closed : continuation_handler -> bool

val binding_code_closed : static_binding -> bool

val code_is_closed : code -> bool
