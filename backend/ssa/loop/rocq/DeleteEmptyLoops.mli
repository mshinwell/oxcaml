open DeadInductionVar
open InductionVar
open LoopTermination
open NaturalLoop
open SsaModel

val body_effect_free : natural_loop -> bool

val single_exit : natural_loop -> block -> bool

val loop_terminates : op_def -> biv list -> bool

val find_deletions : op_def -> block list -> (block * block) list
