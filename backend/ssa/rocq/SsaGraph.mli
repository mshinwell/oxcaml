open SsaModel

val terminator_pure_control : Terminator.t -> bool

val block_effect_free : block -> bool

val is_param : block -> int -> value -> bool

val instr_defines_value : instr -> value -> bool

val args_of_instr : instr -> value list

val terminator_args : Terminator.t -> value list list

val arg_is : value -> Ssa.finished Ssa.Terminator.arg -> bool

val arg_value : Ssa.finished Ssa.Terminator.arg list -> int -> value option

val goto_args : block -> block -> Ssa.finished Ssa.Terminator.arg list option

val goto_passes : block -> int -> value -> block -> bool

val all_uses_ok :
  block list ->
  (value -> bool) ->
  (instr -> bool) ->
  (block -> value list -> bool) ->
  bool

val visit_all :
  (blockset -> block -> blockset option) ->
  blockset ->
  block list ->
  blockset option

val visit_acyclic :
  block list ->
  blockset ->
  block ->
  blockset ->
  blockset ->
  block ->
  blockset option

val acyclic_except : block list -> blockset -> block -> bool
