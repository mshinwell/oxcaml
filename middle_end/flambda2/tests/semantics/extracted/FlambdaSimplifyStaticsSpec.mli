open BinInt
open Datatypes
open FlambdaKindModel
open FlambdaModel
open FlambdaSimplifyApplySpec
open FlambdaSimplifyPrimitivesSpec
open FlambdaSimplifyProjectionsSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv
open List
open ListDef

val static_const_simples : static_const -> simple list

val static_const_type : static_const -> flambda_type list -> flambda_type option

val static_const_type_in : Typing_env.t -> static_const -> flambda_type option

val define_symbol_with_type :
  Typing_env.t -> symbol -> flambda_type -> Typing_env.t

val is_closure_const : static_const -> bool

val closure_symbols_of : static_binding list -> symbol list

val add_block_like_bindings :
  Typing_env.t -> static_binding list -> Typing_env.t

val add_closure_bindings :
  Typing_env.t -> Typing_env.t -> static_binding list -> Typing_env.t

val add_static_bindings : Typing_env.t -> static_binding list -> Typing_env.t
