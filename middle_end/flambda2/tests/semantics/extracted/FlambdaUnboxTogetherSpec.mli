open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open FlambdaUnboxParamsSpec
open FlambdaUnboxVariantsSpec
open FlambdaUntagParamsSpec
open List
open ListDef

val shown_number :
  boxable_number -> variable list -> facts -> simple -> simple option

val unboxed_simple :
  boxable_number -> variable list -> facts -> simple -> simple option

val unbox_arg : boxable_number -> variable list -> facts -> simple -> simple

val together_args :
  boxable_number ->
  nat list ->
  variable list ->
  facts ->
  simple list ->
  simple list

val together_apply_cont :
  boxable_number ->
  positions ->
  variable list ->
  facts ->
  apply_cont ->
  apply_cont

val unbox_of : boxable_number -> named -> variable option

val together_named : boxable_number -> variable list -> named -> named

val together_metadata :
  boxable_number -> nat list -> handler_metadata -> handler_metadata

val together_expr :
  boxable_number ->
  positions ->
  positions ->
  variable list ->
  facts ->
  expr ->
  expr

val together_handler :
  boxable_number ->
  positions ->
  positions ->
  variable list ->
  facts ->
  nat list ->
  continuation_handler ->
  continuation_handler

val unboxed_arg : boxable_number -> variable list -> facts -> simple -> bool

val together_args_ok :
  boxable_number -> variable list -> facts -> nat list -> simple list -> bool

val together_apply_cont_ok :
  boxable_number -> positions -> variable list -> facts -> apply_cont -> bool

val reads_unboxed : boxable_number -> variable list -> named -> bool

val together_named_ok : boxable_number -> variable list -> named -> bool

val together_ok :
  boxable_number ->
  positions ->
  positions ->
  variable list ->
  facts ->
  expr ->
  bool

val together_handler_ok :
  boxable_number ->
  positions ->
  positions ->
  variable list ->
  facts ->
  nat list ->
  continuation_handler ->
  bool

val together_at : boxable_number -> positions -> facts -> expr -> expr

val together_args_blame :
  boxable_number ->
  origin_map ->
  facts ->
  continuation ->
  nat list ->
  nat ->
  simple list ->
  (continuation * nat) list

val together_apply_cont_blame :
  boxable_number ->
  positions ->
  origin_map ->
  facts ->
  apply_cont ->
  (continuation * nat) list

val together_blame :
  boxable_number ->
  positions ->
  positions ->
  origin_map ->
  facts ->
  expr ->
  (continuation * nat) list

val together_handler_blame :
  boxable_number ->
  positions ->
  positions ->
  origin_map ->
  facts ->
  continuation ->
  continuation_handler ->
  (continuation * nat) list

val together_settle :
  boxable_number -> nat -> positions -> facts -> expr -> positions

val together_positions : boxable_number -> facts -> expr -> positions

val unbox_together_of : boxable_number -> facts -> expr -> expr

val unboxed_sorts : expr -> boxable_number list

val handler_unboxed_sorts : continuation_handler -> boxable_number list

val sorts_once :
  boxable_number list -> boxable_number list -> boxable_number list

val unbox_together_all : boxable_number list -> facts -> expr -> expr

val unbox_together_knowing : facts -> expr -> expr
