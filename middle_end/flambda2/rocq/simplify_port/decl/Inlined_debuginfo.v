(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Inlined_debuginfo], after its interface
   middle_end/flambda2/term_basics/inlined_debuginfo.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Code_id Debuginfo Format.

(* inlined_debuginfo.mli:46  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Inlined_debuginfo.t".
(* inlined_debuginfo.mli:48  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Inlined_debuginfo.print".
(* inlined_debuginfo.mli:52  val none : t *)
Parameter none : t.
Extract Inlined Constant none => "Inlined_debuginfo.none".
(* inlined_debuginfo.mli:59  val create : called_code_id:Code_id.t -> apply_dbg:Debuginfo.t -> t *)
Parameter create : Code_id.t -> Debuginfo.t -> M t.
Extract Inlined Constant create => "Inlined_debuginfo.create".
(* inlined_debuginfo.mli:63  val merge : t -> from_apply_expr:t -> t *)
Parameter merge : t -> t -> M t.
Extract Inlined Constant merge => "Inlined_debuginfo.merge".
(* inlined_debuginfo.mli:173  val rewrite : t -> Debuginfo.t -> Debuginfo.t *)
Parameter rewrite : t -> Debuginfo.t -> M Debuginfo.t.
Extract Inlined Constant rewrite => "Inlined_debuginfo.rewrite".
