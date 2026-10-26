open DeadInductionVar
open InductionVar
open LoopTermination
open NaturalLoop
open SsaModel

val terminator_pure_control : Terminator.t -> bool

val body_effect_free : natural_loop -> bool

val find_deletions : op_def -> block list -> (block * block) list
