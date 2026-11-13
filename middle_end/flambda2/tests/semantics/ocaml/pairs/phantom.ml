(* flags: -g -flambda2-expert-phantom-lets *)

(* The first unit of a pair, compiled with the flags of the line above, which
   the tool is given too (README.md). With them Simplify may keep a binding that
   nothing uses as a phantom binding, for a debugger, instead of deleting it;
   the program runs nothing for it. The load of the first field of [b] is one.
   The term that the tool's Simplify makes of this unit has it, and the
   conversion refuses a phantom binding: the unit is not checked. *)

external fst : 'a * 'b -> 'a = "%field0"

let[@inline] f b =
  let x = fst b in
  let _unused = x in
  0
