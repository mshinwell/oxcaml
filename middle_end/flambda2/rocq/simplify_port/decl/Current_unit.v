(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Current_unit], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Compilation_unit.

(* current_unit.mli:21  val get_cu_exn : unit -> Compilation_unit.t *)
Parameter get_cu_exn : unit -> M Compilation_unit.t.
Extract Inlined Constant get_cu_exn => "Current_unit.get_cu_exn".
