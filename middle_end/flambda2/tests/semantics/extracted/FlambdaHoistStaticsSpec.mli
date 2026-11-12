open Datatypes
open FlambdaModel
open FlambdaSemanticsSpec
open FlambdaStaticsInScopeSpec
open FlambdaWellFormedSpec
open List

val is_hoisted : static_binding -> bool

val hoisted_bindings : expr -> static_binding list

val handler_hoisted_bindings : continuation_handler -> static_binding list

val without_hoisted : expr -> expr

val handler_without_hoisted : continuation_handler -> continuation_handler

val hoist_statics : unit_interface -> expr -> expr option
