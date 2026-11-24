(* This file follows an interface whose source was not found: see the
   comment below. *)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Lambda], after its interface
   (source not found)
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9. Made by tools/declgen (see decl/README.md): a
   change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Clflags Location.

(* lambda.mli:49  type return_mode = private | Maybe_alloc_stack | Not_alloc_stack *)
Inductive return_mode : Type :=
| Maybe_alloc_stack : return_mode
| Not_alloc_stack : return_mode.
(* lambda.mli:144  type lazy_block_tag = | Lazy_tag | Forward_tag *)
Parameter lazy_block_tag : Type.
Extract Inlined Constant lazy_block_tag => "Lambda.lazy_block_tag".
(* lambda.mli:860  type zero_alloc_attribute = | Default_zero_alloc | Check of { strict: bool; ( * [strict=true] property holds on all paths. [strict=false] if the function returns normally, then the property holds (but property violations on exceptional returns or divering loops are ignored). This definition may not be applicable to new properties. * ) loc: Location.t; custom_error_msg: string option; partial: b... *)
Record check_payload_ : Type := { strict : bool; loc : Location.t; custom_error_msg : option string; partial : bool }.
(* The inline record of [Assume]: abstract (a name of its fields is taken, or it holds the type); [mk_Assume] makes one, [match_zero_alloc_attribute] reads it. *)
Parameter assume_payload_ : Type.
Inductive zero_alloc_attribute : Type :=
| Default_zero_alloc : zero_alloc_attribute
| Check : check_payload_ -> zero_alloc_attribute
| Assume : assume_payload_ -> zero_alloc_attribute.
Parameter mk_Default_zero_alloc : zero_alloc_attribute.
Extract Inlined Constant mk_Default_zero_alloc => "Lambda.Default_zero_alloc".
Parameter mk_Check : bool -> Location.t -> option string -> bool -> zero_alloc_attribute.
Extract Inlined Constant mk_Check => "(fun x__1 x__2 x__3 x__4 -> Lambda.Check { strict = x__1; loc = x__2; custom_error_msg = x__3; partial = x__4 })".
Parameter mk_Assume : bool -> bool -> bool -> Location.t -> zero_alloc_attribute.
Extract Inlined Constant mk_Assume => "(fun x__1 x__2 x__3 x__4 -> Lambda.Assume { strict = x__1; never_returns_normally = x__2; never_raises = x__3; loc = x__4 })".
Parameter match_zero_alloc_attribute : forall {Res : Type}, zero_alloc_attribute -> (unit -> M Res) -> (bool -> Location.t -> option string -> bool -> M Res) -> (bool -> bool -> bool -> Location.t -> M Res) -> M Res.
Extract Inlined Constant match_zero_alloc_attribute => "(fun x__0 f__1 f__2 f__3 -> match x__0 with Lambda.Default_zero_alloc -> f__1 () | Lambda.Check { strict = x__1; loc = x__2; custom_error_msg = x__3; partial = x__4 } -> f__2 x__1 x__2 x__3 x__4 | Lambda.Assume { strict = x__1; never_returns_normally = x__2; never_raises = x__3; loc = x__4 } -> f__3 x__1 x__2 x__3 x__4)".
(* lambda.mli:883  type regalloc_attribute = | Default_regalloc | Regalloc of Clflags.Register_allocator.t *)
Inductive regalloc_attribute : Type :=
| Default_regalloc : regalloc_attribute
| Regalloc : Clflags.Register_allocator.t -> regalloc_attribute.
(* lambda.mli:886  type regalloc_param_attribute = | Default_regalloc_params | Regalloc_params of string list *)
Inductive regalloc_param_attribute : Type :=
| Default_regalloc_params : regalloc_param_attribute
| Regalloc_params : list string -> regalloc_param_attribute.
