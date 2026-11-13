open BinPos
open Datatypes
open FlambdaKindModel
open FlambdaMapSpec
open FlambdaModel
open FlambdaNormaliseSpec
open FlambdaPrimitiveModel
open List
open ListDef
open PeanoNat

type positions = (continuation * nat list) list

val positions_of : positions -> continuation -> nat list

val at_position : nat list -> nat -> bool

val kept_from : nat list -> nat -> 'a1 list -> 'a1 list

val moved_from : nat list -> nat -> 'a1 list -> 'a1 list

val untagged_kind : flambda_kind

val untag_simple : simple -> simple

val untag_args : nat list -> simple list -> simple list

val untag_apply_cont : positions -> apply_cont -> apply_cont

val untag_of : named -> variable option

val untag_named : variable list -> named -> named

val untag_params_list : nat list -> variable list -> variable list

val untag_metadata : nat list -> handler_metadata -> handler_metadata

val untagged_under : nat list -> variable list -> variable list -> variable list

val active_under :
  positions ->
  (continuation * continuation_handler) list ->
  positions ->
  positions

val untag_expr : positions -> positions -> variable list -> expr -> expr

val untag_handler :
  positions ->
  positions ->
  variable list ->
  nat list ->
  continuation_handler ->
  continuation_handler

val none_in : variable list -> (variable -> bool) -> bool

val untagged_arg : variable list -> simple -> bool

val args_ok : variable list -> nat list -> simple list -> bool

val apply_cont_ok : positions -> variable list -> apply_cont -> bool

val reads_untagged : variable list -> named -> bool

val named_ok : variable list -> named -> bool

val no_positions : positions -> continuation -> bool

val handler_fits : nat list -> variable list -> handler_metadata -> bool

val untag_ok : positions -> positions -> variable list -> expr -> bool

val handler_ok :
  positions ->
  positions ->
  variable list ->
  nat list ->
  continuation_handler ->
  bool

val untag_at : positions -> expr -> expr

val value_positions : nat -> flambda_kind list -> nat list

val candidates : expr -> positions

val handler_candidates : continuation -> continuation_handler -> positions

type origin_map = (variable * (continuation * nat)) list

val origins : origin_map -> (variable -> bool) -> (continuation * nat) list

val all_of : positions -> continuation -> (continuation * nat) list

val params_origins :
  continuation -> nat list -> nat -> variable list -> origin_map

val origins_under :
  continuation -> nat list -> variable list -> origin_map -> origin_map

val args_blame :
  origin_map ->
  continuation ->
  nat list ->
  nat ->
  simple list ->
  (continuation * nat) list

val apply_cont_blame :
  positions -> origin_map -> apply_cont -> (continuation * nat) list

val blame :
  positions -> positions -> origin_map -> expr -> (continuation * nat) list

val handler_blame :
  positions ->
  positions ->
  origin_map ->
  continuation ->
  continuation_handler ->
  (continuation * nat) list

val blamed : (continuation * nat) list -> continuation -> nat -> bool

val prune : (continuation * nat) list -> positions -> positions

val settle_positions : nat -> positions -> expr -> positions

val count_positions : positions -> nat

val untag_positions : expr -> positions

val untag_params : expr -> expr
