open BinNums
open BinPos
open Datatypes
open FlambdaBlockLoadSpec
open FlambdaCseSpec
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaUnboxSpec
open List
open ListDef
open PeanoNat

val reads_a_box : unary_primitive -> bool

type facts =
  { facts_blocks : known_blocks;
    facts_numbers : known_numbers;
    facts_reads : computed
  }

val no_facts : facts

val reads_under_let : computed -> variable -> named -> computed

val facts_under_let : facts -> variable -> named -> facts

val facts_under_statics : facts -> static_binding list -> facts

val facts_under_params : facts -> variable list -> facts

val projection_of : facts -> unary_primitive -> simple -> simple option

val extend_args :
  facts -> nat -> unary_primitive -> simple list -> simple list option

val all_some : 'a1 option list -> 'a1 list option

val extend_apply_cont_by :
  (facts -> simple list -> simple list option) ->
  facts ->
  continuation ->
  apply_cont ->
  apply_cont option

val extend_arms_by :
  (facts -> simple list -> simple list option) ->
  facts ->
  continuation ->
  (coq_Z * apply_cont) list ->
  (coq_Z * apply_cont) list option

val extend_applications_by :
  (facts -> simple list -> simple list option) ->
  facts ->
  continuation ->
  expr ->
  expr option

val extend_in_handler_by :
  (facts -> simple list -> simple list option) ->
  facts ->
  continuation ->
  continuation_handler ->
  continuation_handler option

val position : variable -> variable list -> nat option

val may_take : variable list -> handler_metadata -> variable -> bool

val with_one_more : handler_metadata -> flambda_kind -> handler_metadata
