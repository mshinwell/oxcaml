(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Switch_arm], after its interface
   middle_end/flambda2/terms/switch_arm.mli
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_expr Branch_annotations.

(* switch_arm.mli:29  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Switch_arm.t".
(* switch_arm.mli:35  val create : annotations:Branch_annotations.t -> Apply_cont_expr.t -> t *)
Parameter create : Branch_annotations.t -> Apply_cont_expr.t -> M t.
Extract Inlined Constant create => "Switch_arm.create".
(* switch_arm.mli:39  val annotations : t -> Branch_annotations.t *)
Parameter annotations : t -> M Branch_annotations.t.
Extract Inlined Constant annotations => "Switch_arm.annotations".
(* switch_arm.mli:41  val action : t -> Apply_cont_expr.t *)
Parameter action : t -> M Apply_cont_expr.t.
Extract Inlined Constant action => "Switch_arm.action".
(* switch_arm.mli:47  val is_cold : t -> bool *)
Parameter is_cold : t -> M bool.
Extract Inlined Constant is_cold => "Switch_arm.is_cold".
