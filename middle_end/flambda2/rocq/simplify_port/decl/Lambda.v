(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Lambda], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.

(* lambda.mli:49  type return_mode = private | Maybe_alloc_stack | Not_alloc_stack *)
Parameter return_mode : Type.
Extract Inlined Constant return_mode => "Lambda.return_mode".
(* lambda.mli:860  type zero_alloc_attribute = | Default_zero_alloc | Check of { strict: bool; ( * [strict=true] property holds on all paths. [strict=false] if the function returns normally, then the property holds (but property violations on exceptional returns or divering loops are ignored). This definition may not be applicable to new properties. * ) loc: Location.t; custom_error_msg: string option; partial: b... *)
Parameter zero_alloc_attribute : Type.
Extract Inlined Constant zero_alloc_attribute => "Lambda.zero_alloc_attribute".
(* lambda.mli:883  type regalloc_attribute = | Default_regalloc | Regalloc of Clflags.Register_allocator.t *)
Parameter regalloc_attribute : Type.
Extract Inlined Constant regalloc_attribute => "Lambda.regalloc_attribute".
(* lambda.mli:886  type regalloc_param_attribute = | Default_regalloc_params | Regalloc_params of string list *)
Parameter regalloc_param_attribute : Type.
Extract Inlined Constant regalloc_param_attribute => "Lambda.regalloc_param_attribute".
