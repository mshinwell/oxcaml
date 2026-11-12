open Datatypes
open FlambdaBlockLoadSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaUnboxParamsSpec
open FlambdaUnboxSpec
open ListDef

val closed_field : simple option -> simple option

val facts_of_symbols : facts -> facts

val symbols_under_statics : facts -> static_binding list -> facts

val rewrite_code_in_scope : (facts -> expr -> expr) -> facts -> expr -> expr

val rewrite_code_in_scope_in_handler :
  (facts -> expr -> expr) ->
  facts ->
  continuation_handler ->
  continuation_handler

val rewrite_rec_handlers_in_scope :
  (facts -> expr -> expr) -> facts -> expr -> expr

val rewrite_rec_handlers_in_scope_in_handler :
  (facts -> expr -> expr) ->
  facts ->
  continuation_handler ->
  continuation_handler

val rewrite_rec_handler_in_scope :
  (facts -> expr -> expr) ->
  facts ->
  continuation_handler ->
  continuation_handler
