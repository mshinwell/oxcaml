(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Debuginfo], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Format Location.

(* debuginfo.mli:97  type t *)
Parameter t : Type.
Extract Inlined Constant t => "Debuginfo.t".
(* debuginfo.mli:99  val none : t *)
Parameter none : t.
Extract Inlined Constant none => "Debuginfo.none".
(* debuginfo.mli:113  val to_location : t -> Location.t *)
Parameter to_location : t -> M Location.t.
Extract Inlined Constant to_location => "Debuginfo.to_location".
(* debuginfo.mli:132  val print_compact : Format.formatter -> t -> unit *)
Parameter print_compact : Format.formatter -> t -> M unit.
Extract Inlined Constant print_compact => "Debuginfo.print_compact".
(* debuginfo.mli:140  val merge : into:t -> t -> t *)
Parameter merge : t -> t -> M t.
Extract Inlined Constant merge => "Debuginfo.merge".
