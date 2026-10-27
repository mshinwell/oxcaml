open NaturalLoop
open SsaModel

val is_header_param : block -> int -> value -> bool

val strictly_dominates : block -> block -> bool

val is_loop_invariant : op_def -> block -> value -> bool

type biv_step =
  | Step_const of int
  | Step_var of value

type biv =
  { loop : natural_loop;
    param_index : int;
    update : value list;
    step : biv_step;
    sign : [`Add | `Sub]
  }

val step_same : biv_step -> biv_step -> bool

val sign_same : [`Add | `Sub] -> [`Add | `Sub] -> bool

val signed_step : biv -> int option

val classify_update :
  (value -> bool) ->
  op_def ->
  block ->
  value ->
  (biv_step * [`Add | `Sub]) option

val back_edge_set : natural_loop -> blockset

val pred_args_to_header :
  block -> block -> Ssa.finished Ssa.Terminator.arg list option

val arg_value : Ssa.finished Ssa.Terminator.arg list -> int -> value option

val classify_param :
  natural_loop ->
  op_def ->
  (block * Ssa.finished Ssa.Terminator.arg list) list ->
  int ->
  biv option

val params_bivs :
  natural_loop ->
  op_def ->
  (block * Ssa.finished Ssa.Terminator.arg list) list ->
  int ->
  value list ->
  biv list

val analyze_loop : op_def -> natural_loop -> biv list

val analyze : op_def -> block list -> (natural_loop * biv list) list
