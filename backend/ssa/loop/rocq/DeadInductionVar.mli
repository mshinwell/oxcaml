open InductionVar
open LoopTermination
open NaturalLoop
open SsaModel

type biv_result =
  { biv : biv;
    dead : bool
  }

type loop_result =
  { loop : natural_loop;
    bivs : biv_result list;
    useless : bool
  }

val instr_defines_value : instr -> value -> bool

val args_of_instr : instr -> value list

val terminator_args : Terminator.t -> value list list

val count_occurrences : ('a1 -> bool) -> 'a1 list -> int

val all_uses_ok :
  block list ->
  (value -> bool) ->
  (instr -> bool) ->
  (block -> value list -> bool) ->
  bool

val arg_is : value -> Ssa.finished Ssa.Terminator.arg -> bool

val goto_passes : block -> int -> value -> block -> bool

val is_dead : block list -> biv -> bool

val loop_is_useless : natural_loop -> biv_result list -> bool

val analyze : block list -> (natural_loop * biv list) list -> loop_result list
