open Datatypes
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaSemanticsSpec
open FlambdaValueSpec
open List
open ListDef
open OxCamlOption

val closed_simple : simple -> bool

val closed_static_const : static_const -> bool

val known_of_binding : static_binding -> (symbol * static_const) list

val known_bindings : expr -> (symbol * static_const) list

val known_bindings_of_handler :
  continuation_handler -> (symbol * static_const) list

val known_value :
  symbol * static_const -> (symbol * statically_allocated_value) list

val known_statics : (symbol * static_const) list -> static_env

val set_of_binding : static_binding -> (symbol * static_const) list

val known_sets : expr -> (symbol * static_const) list

val known_sets_of_handler : continuation_handler -> (symbol * static_const) list

val simple_known : static_env -> simple -> bool

val named_known : static_env -> named -> bool

val fold_known_named : static_env -> named -> named

val fold_function_slot : static_env -> named -> named

val fold_known : static_env -> static_env -> expr -> expr

val fold_known_handler :
  static_env -> static_env -> continuation_handler -> continuation_handler

val fold_known_binding :
  static_env -> static_env -> static_binding -> static_binding

val fold_known_code : static_env -> static_env -> code -> code

val binding_bound_as :
  (symbol * static_const) list ->
  (symbol * static_const) list ->
  static_binding ->
  bool

val bound_as :
  (symbol * static_const) list -> (symbol * static_const) list -> expr -> bool

val handler_bound_as :
  (symbol * static_const) list ->
  (symbol * static_const) list ->
  continuation_handler ->
  bool

val code_of_binding_bound_as :
  (symbol * static_const) list ->
  (symbol * static_const) list ->
  static_binding ->
  bool

val code_bound_as :
  (symbol * static_const) list -> (symbol * static_const) list -> code -> bool

val fold_known_unit : expr -> expr option
