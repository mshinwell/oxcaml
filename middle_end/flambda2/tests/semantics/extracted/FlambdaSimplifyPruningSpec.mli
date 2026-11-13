open BinNums
open BinPos
open Datatypes
open FlambdaEnvAliasesInvariantSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaPrimitiveSpec
open FlambdaSimplifyPassSpec
open FlambdaSimplifyPrimitivesSpec
open FlambdaSimplifyStaticsSpec
open FlambdaTypeGrammar
open FlambdaTypingEnv
open List
open ListDef
open OxCamlOption

val alias_keeps_fit : Typing_env.t -> simple -> simple -> flambda_kind -> bool

val equation_keeps_fit : Typing_env.t -> name -> flambda_type -> bool

val block_like_bindings_keep_fit : Typing_env.t -> static_binding list -> bool

val closure_bindings_keep_fit :
  Typing_env.t -> Typing_env.t -> static_binding list -> bool

val statics_keep_fit : Typing_env.t -> static_binding list -> bool

val arm_env_keeps_fit : Typing_env.t -> simple -> coq_Z -> bool

val leaf_uses_keep_fit : Typing_env.t -> continuation -> expr -> bool
