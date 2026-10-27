open InductionVar
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

val param_uses_ok : block list -> block -> int -> value -> value list -> bool

val cond_uses_ok : block list -> block -> value -> bool

val update_uses_ok :
  block list -> block -> blockset -> int -> value -> value -> bool

val is_dead : block list -> biv -> bool

val loop_is_useless : natural_loop -> biv_result list -> bool

val analyze : block list -> (natural_loop * biv list) list -> loop_result list
