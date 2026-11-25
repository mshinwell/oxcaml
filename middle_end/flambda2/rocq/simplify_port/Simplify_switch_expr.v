(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2020 OCamlPro SAS                                    *)
(*   Copyright 2014--2020 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/simplify_switch_expr.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the types with an inline record and
   the polymorphic variants as Rocq inductive types with their extraction)
   is that of GUIDE.md; the abbreviation [rebuilder] for a type that the
   compiler does not name; the names of the arguments that the compiler
   takes apart in its patterns. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Simplified_expr Simplify_simple.
From SimplifyPort.decl Require Alloc_mode Apply_cont_rewrite_id
  Are_lifting_conts Are_rebuilding_terms Bound_parameters
  Branch_annotations Code_size Coercion
  Common_subexpression_elimination Continuation Continuation_in_env
  Continuation_uses Cost_metrics Current_unit Debuginfo Flambda
  Flambda2_types Flambda_arity Flambda_debug_uid Flambda_features
  Flambda_kind Flambda_primitive Float Flow Int_ids Likelihood List
  ListLabels Mutability Name Option Or_bottom Or_unknown
  Or_unknown_or_bottom Or_variable Profile Reg_width_const
  Removed_operations Simple Simplified_named Simplify_apply_cont_expr
  Simplify_common Specialization_cost Static_const Stdlib_ String Switch_arm
  Symbol Target_ocaml_int Target_system Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Are_lifting_conts.t
   Expr_builder.rewrite_switch_arm_result Flambda.Invalid.t
   Flambda.static_const_or_code
   Flambda2_types.Join_analysis.simple_refined_at_join_
   Flambda_kind.Naked_number_kind.t Flambda_kind.t
   Flambda_primitive.Array_load_kind.t
   Flambda_primitive.binary_float_arith_op
   Flambda_primitive.binary_primitive Flambda_primitive.unary_primitive
   Int_ids.Const.Descr.t Mutability.t Or_bottom.t Or_unknown.t
   Or_unknown_or_bottom.t Simplify_common.apply_cont_context
   Specialization_cost.reason Specialization_cost.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 18-21 *)
From SimplifyPort.abbrev.simplify_switch_expr Require Import Port_abbreviations.
(*OCAML
module TE = Flambda2_types.Typing_env
module TI = Target_ocaml_int
module Alias_set = TE.Alias_set
module RWC = Reg_width_const
OCAML*)

(*OCAML
exception Argument_cannot_be_used_in_lookup_table
OCAML*)

(* 23-25 *)
Inductive alias_set : Type :=
| Aliases (_ : Alias_set.t)
| Poison (_ : Flambda_kind.t).

(* 27-33 *)
(* PORT-GAP(type): [Mergeable] has an inline record: its fields are taken by
   place, and the compiler's definition is the text that Rocq prints. *)
Inductive mergeable_arms_ : Type :=
| No_arms
| Mergeable (cont : Continuation.t) (args : list (TI.Map.t alias_set))
| Not_mergeable.
Extract Inductive mergeable_arms_ => "mergeable_arms" [ "No_arms" "(fun (x__1, x__2) -> Mergeable { cont = x__1; args = x__2 })" "Not_mergeable" ] "(fun f__1 f__2 f__3 x__0 -> match x__0 with No_arms -> f__1 () | Mergeable { cont = x__1; args = x__2 } -> f__2 x__1 x__2 | Not_mergeable -> f__3 ())".
Definition mergeable_arms : Type := mergeable_arms_.
Extract Constant mergeable_arms => "| No_arms | Mergeable of { cont : Continuation.t; args : alias_set TI.Map.t list } | Not_mergeable".

(* 35-46 *)
Definition inter_alias_set (alias1 alias2 : alias_set) : M alias_set :=
  match alias1, alias2 with
  | Aliases alias1, Aliases alias2 =>
    let! tmp1 := Alias_set.inter alias1 alias2 in
    ret (Aliases tmp1)
  | Aliases alias, Poison _ | Poison _, Aliases alias => ret (Aliases alias)
  | Poison kind1, Poison kind2 =>
    let! tmp1 := Flambda_kind.equal kind1 kind2 in
    if tmp1
    then ret (Poison kind1)
    else
      fatal_errorf4
        "[inter_alias_set]: intersection of poison with different kinds %a and %a"
        Flambda_kind.print kind1 Flambda_kind.print kind2
  end.

(* 48-80. [Simple.pattern_match' ~var ~symbol ~const arg]: the arguments are
   in the order of the interface. *)
Definition find_all_aliases (env : TE.t) (arg : Simple.t) : M alias_set :=
  let& find_all_aliases :=
    fun (_ : unit) =>
    let! tmp1 := TE.aliases_of_simple env NM.normal arg in
    ret (Aliases tmp1)
  in
  Simple.pattern_match' arg
    (fun _var (_ : Coercion.t) =>
      (* We use find alias to find a common simple to different simples.

         This simple is already guaranteed to be the cannonical alias.

         * If there is a common alias between variables, the cannonical alias
         must also be a common alias.

         * For constants and symbols there can be a common alias that is not
         cannonical: A variable can have different constant values in different
         branches: this variable is not the cannonical alias, the cannonical
         would be the constant or the symbol. But the only common alias could be
         a variable in that case.

         hence there is no loss of generality in returning the cannonical alias
         as the single alias if it is a variable.

         Note that the main reason for this is to allow changing the arguments
         of continuations to variables that where not in scope during the
         downward traversal. In particular for the alias rewriting provided by
         data_flow *)
      let! tmp1 := TE.Alias_set.singleton arg in
      ret (Aliases tmp1))
    (fun _sym (_ : Coercion.t) => find_all_aliases tt)
    (fun cst =>
      let! tmp1 := Reg_width_const.is_poison cst in
      match tmp1 with
      | Some (kind, _name) => ret (Poison kind)
      | None => find_all_aliases tt
      end).

(* 82-179. In the compiler the third and the fourth argument are the
   patterns [(action, ~annotations, use_id, arity, env_at_use)] and
   [(new_let_conts, arms, (mergeable_arms : mergeable_arms))]. *)
Definition rebuild_arm (uacc : UA.t) (arm : TI.t) (pat : SE.arms_tuple)
    (pat0 : tuple3 (list EB.new_let_cont) (TI.Map.t Switch_arm.t)
              mergeable_arms)
    : M (tuple3 (list EB.new_let_cont) (TI.Map.t Switch_arm.t)
           mergeable_arms) :=
  let* '(SE.Arms_tuple action annotations use_id arity env_at_use) :=
    ret pat
  in
  let* '(T3 new_let_conts arms mergeable_arms) := ret pat0 in
  (* 84-87 *)
  let* action :=
    Simplify_common.clear_demoted_trap_action_and_patch_unused_exn_bucket uacc
      action
  in
  (* 88-95 *)
  let& create_arm :=
    fun (action : Apply_cont.t) =>
    let* annotations :=
      let! tmp1 := Apply_cont.continuation action in
      let! tmp2 := UA.uenv uacc in
      let! tmp3 := UE.is_cold_continuation tmp2 tmp1 in
      if tmp3
      then Branch_annotations.with_likelihood annotations Likelihood.cold
      else ret annotations
    in
    Switch_arm.create annotations action
  in
  (* 96 *)
  let! tmp1 := EB.rewrite_switch_arm uacc action use_id arity in
  match tmp1 with
  | EB.Invalid_ _ =>
    (* The destination is unreachable; delete the [Switch] arm. *)
    ret (T3 new_let_conts arms mergeable_arms)
  | EB.Apply_cont_ action =>
    (* 101-142 *)
    let* action :=
      let* cont := Apply_cont.continuation action in
      let* cont_info_from_uenv :=
        let! tmp1 := UA.uenv uacc in
        UE.find_continuation tmp1 cont
      in
      (* First try to absorb any [Apply_cont] expression that forms the entirety
         of the arm's action (via an intermediate zero-arity continuation
         without trap action) into the [Switch] expression itself. *)
      match cont_info_from_uenv with
      | Continuation_in_env.Invalid _ => ret None
      | Continuation_in_env.Linearly_used_and_inlinable _ _ _ _
      | Continuation_in_env.Non_inlinable_zero_arity _
      | Continuation_in_env.Non_inlinable_non_zero_arity _
      | Continuation_in_env.Toplevel_or_function_return_or_exn_continuation _ =>
        let! tmp1 := Apply_cont.is_goto action in
        if negb tmp1
        then ret (Some action)
        else
          let& check_handler :=
            fun (handler : RE.t) (action : Apply_cont.t) =>
            let! tmp1 := RE.to_apply_cont handler in
            match tmp1 with
            | Some action => ret (Some action)
            | None => ret (Some action)
            end
          in
          match cont_info_from_uenv with
          | Continuation_in_env.Linearly_used_and_inlinable params handler _ _ =>
            (let! tmp1 := Bound_parameters.is_empty params in
             assert_ tmp1) ;;
            check_handler handler action
          | Continuation_in_env.Non_inlinable_zero_arity
              (Or_unknown.Known handler) =>
            check_handler handler action
          | Continuation_in_env.Non_inlinable_zero_arity Or_unknown.Unknown =>
            ret (Some action)
          | Continuation_in_env.Invalid _ => ret None
          | Continuation_in_env.Toplevel_or_function_return_or_exn_continuation
              _ =>
            (* It is legal to call a return continuation with zero arguments; it
               might originally have had layout [void] *)
            ret (Some action)
          | Continuation_in_env.Non_inlinable_non_zero_arity _ =>
            fatal_errorf4
              "Inconsistency for %a between [Apply_cont.is_goto] and continuation environment in [UA]:@ %a"
              Continuation.print cont UA.print uacc
          end
      end
    in
    (* 143-174 *)
    match action with
    | None =>
      (* The destination is unreachable; delete the [Switch] arm. *)
      ret (T3 new_let_conts arms mergeable_arms)
    | Some action =>
      let* arms :=
        let! tmp1 := create_arm action in
        TI.Map.add arm tmp1 arms
      in
      (* Check to see if this arm may be merged with others. *)
      let! tmp1 := Apply_cont.trap_action action in
      let! tmp2 := Option.is_some tmp1 in
      if tmp2
      then ret (T3 new_let_conts arms Not_mergeable)
      else
        match mergeable_arms with
        | Not_mergeable => ret (T3 new_let_conts arms Not_mergeable)
        | No_arms =>
          let* cont := Apply_cont.continuation action in
          let* args :=
            let! tmp1 := Apply_cont.args action in
            List.map
              (fun arg =>
                let! tmp2 := find_all_aliases env_at_use arg in
                TI.Map.singleton arm tmp2)
              tmp1
          in
          ret (T3 new_let_conts arms (Mergeable cont args))
        | Mergeable cont args =>
          let! tmp1 := Apply_cont.continuation action in
          let! tmp2 := Continuation.equal cont tmp1 in
          if negb tmp2
          then ret (T3 new_let_conts arms Not_mergeable)
          else
            let* args :=
              let! tmp1 := Apply_cont.args action in
              List.map2
                (fun arg_set arg =>
                  let! tmp2 := find_all_aliases env_at_use arg in
                  TI.Map.add arm tmp2 arg_set)
                args tmp1
            in
            ret (T3 new_let_conts arms (Mergeable cont args))
        end
    end
  | EB.New_wrapper new_let_cont =>
    (* 176-179 *)
    let& new_let_conts := new_let_cont :: new_let_conts in
    let* action := Apply_cont.goto new_let_cont.(Expr_builder.cont) in
    let* arms :=
      let! tmp1 := create_arm action in
      TI.Map.add arm tmp1 arms
    in
    ret (T3 new_let_conts arms Not_mergeable)
  end.

(* 181-192. [Simple.pattern_match alias ~name ~const]: the arguments are in
   the order of the interface. *)
Definition filter_and_choose_alias (required_names : Name.Set_.t)
    (alias_set : alias_set) : M (option Simple.t) :=
  match alias_set with
  | Poison kind =>
    let! tmp1 := Reg_width_const.const_poison kind "rebuild_switch" in
    let! tmp2 := Simple.const tmp1 in
    ret (Some tmp2)
  | Aliases alias_set =>
    let* available_alias_set :=
      Alias_set.filter alias_set
        (fun alias =>
          Simple.pattern_match alias
            (fun name (_ : Int_ids.Coercion.t) =>
              Name.Set_.mem name required_names)
            (fun _ => ret true))
    in
    Alias_set.find_best available_alias_set
  end.

(* 194-217 *)
(* PORT-GAP(loose): 194, the optional parameter [?(required = true)] is
   [required : option bool] by place, and its default is the first line of
   the body; the function is not in the interface, so it has no wrapper
   with the label. 199, the attribute [@local] is not kept. *)
Definition find_cse_simple (required : option bool)
    (cse : Common_subexpression_elimination.t) (typing_env : TE.t)
    (required_names : Name.Set_.t)
    (local_cse : Common_subexpression_elimination.t) (prim : P.t)
    : M (option Simple.t) :=
  let& required :=
    match required with Some required => required | None => true end
  in
  let! tmp1 := P.Eligible_for_cse.create prim in
  match tmp1 with
  | None => ret None (* Constant *)
  | Some with_fixed_value =>
    let& try_local_cse :=
      fun (_ : unit) =>
      Common_subexpression_elimination.find local_cse with_fixed_value
    in
    let! tmp1 := Common_subexpression_elimination.find cse with_fixed_value in
    match tmp1 with
    | None =>
      if required
      then
        fatal_errorf2
          "Expected@ primitive@ not@ found@ in@ CSE@ environment@ while@ simplifying switch:@ %a"
          P.print prim
      else try_local_cse tt
    | Some simple =>
      let! tmp1 := find_all_aliases typing_env simple in
      let! tmp2 := filter_and_choose_alias required_names tmp1 in
      match tmp2 with
      | Some simple => ret (Some simple)
      | None => try_local_cse tt
      end
    end
  end.

(* 219-220 *)
Definition fields_to_simples (dbg : Debuginfo.t) (simples : list Simple.t)
    : M (list Simple.With_debuginfo.t) :=
  List.map (fun simple => Simple.With_debuginfo.create simple dbg) simples.

(* 224-252 *)
(* PORT-GAP(loose): in the compiler [fields_to_or_variables] and
   [naked_number_array] are local functions of
   [create_lookup_table_array_const], used there at several types of
   constants. A local function of Rocq has one type (the extraction would
   write [Obj.magic]): the two are definitions of the file, and what they
   use of the function around them is their first arguments. *)
Definition fields_to_or_variables {A : Type} (dbg : Debuginfo.t)
    (machine_width : Target_system.Machine_width.t)
    (prover : RWC.t -> M (option A)) (simples : list Simple.t)
    : M (list (Or_variable.t A)) :=
  ListLabels.map
    (fun simple =>
      Simple.pattern_match simple
        (fun _ (_ : Int_ids.Coercion.t) =>
          (* Only constants reach this point. *) assert_false)
        (fun cst =>
          let* cst :=
            (* Poison values can't be represented in static const arrays, so
               we materialize them as an arbitrary value here.

               We lose the information that the value is a poison for later
               simplifications, which is unfortunate, but the benefit in code
               size is likely worth it compared to not using lookup tables for
               values that could be poisoned. *)
            let! tmp1 := RWC.is_poison cst in
            match tmp1 with
            | None => ret cst
            | Some (kind, name) =>
              let! tmp1 := String.hash name in
              RWC.of_int_of_kind machine_width kind tmp1
            end
          in
          let* cst :=
            let! tmp1 := prover cst in
            match tmp1 with
            | Some v => ret v
            | None =>
              fatal_errorf4
                "Unexpected kind of constant (%a) in switch table at %a"
                RWC.print cst Debuginfo.print_compact dbg
            end
          in
          ret (Or_variable.Const cst)))
    simples.

(* 253-255 *)
Definition naked_number_array {A : Type} (dbg : Debuginfo.t)
    (rebuilding : Are_rebuilding_terms.t) (simples : list Simple.t)
    (machine_width : Target_system.Machine_width.t)
    (creator : Are_rebuilding_terms.t -> list (Or_variable.t A) -> M RSC.t)
    (prover : RWC.t -> M (option A)) : M RSC.t :=
  let! tmp1 := fields_to_or_variables dbg machine_width prover simples in
  creator rebuilding tmp1.

(* 222-287. In the compiler: [dbg array_kind rebuilding simples
   ~machine_width]. The local [naked_number_array creator prover] of the
   compiler is [naked_number_array dbg rebuilding simples machine_width
   creator prover] here (see above). *)
Definition create_lookup_table_array_const (dbg : Debuginfo.t)
    (array_kind : P.Array_kind.t) (rebuilding : Are_rebuilding_terms.t)
    (simples : list Simple.t) (machine_width : Target_system.Machine_width.t)
    : M RSC.t :=
  match array_kind with
  | P.Array_kind.Values | P.Array_kind.Immediates =>
    let! tmp1 := fields_to_simples dbg simples in
    RSC.create_immutable_value_array rebuilding tmp1
  | P.Array_kind.Naked_float32s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_float32_array RWC.is_naked_float32
  | P.Array_kind.Naked_floats =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_float_array RWC.is_naked_float
  | P.Array_kind.Naked_ints =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_int_array RWC.is_naked_immediate
  | P.Array_kind.Naked_int8s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_int8_array RWC.is_naked_int8
  | P.Array_kind.Naked_int16s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_int16_array RWC.is_naked_int16
  | P.Array_kind.Naked_int32s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_int32_array RWC.is_naked_int32
  | P.Array_kind.Naked_int64s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_int64_array RWC.is_naked_int64
  | P.Array_kind.Naked_nativeints =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_nativeint_array RWC.is_naked_nativeint
  | P.Array_kind.Naked_vec128s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_vec128_array RWC.is_naked_vec128
  | P.Array_kind.Naked_vec256s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_vec256_array RWC.is_naked_vec256
  | P.Array_kind.Naked_vec512s =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_vec512_array RWC.is_naked_vec512
  | P.Array_kind.Naked_masks =>
    naked_number_array dbg rebuilding simples machine_width
      RSC.create_immutable_mask_array RWC.is_naked_mask
  | P.Array_kind.Gc_ignorable_values | P.Array_kind.Unboxed_product _ =>
    fatal_errorf4
      "Unexpected array kind %a when rebuilding switch lookup table at %a"
      P.Array_kind.print array_kind Debuginfo.print_compact dbg
  end.

(* Tiny DSL to preserve sanity while rebuilding expressions. *)

(* 291-300 *)
(* PORT-GAP(type): [Lookup_table] has an inline record: its fields are taken
   by place, and the compiler's definition is the text that Rocq prints. *)
Inductive named_ : Type :=
| Simple (_ : Simple.t)
| Prim (_ : string) (_ : K.t) (_ : P.t) (_ : Debuginfo.t)
| Lookup_table (name : string) (array_kind : P.Array_kind.t)
    (element_kind : KS.t) (simples : list Simple.t) (dbg : Debuginfo.t).
Extract Inductive named_ => "named" [ "Simple" "Prim" "(fun (x__1, x__2, x__3, x__4, x__5) -> Lookup_table { name = x__1; array_kind = x__2; element_kind = x__3; simples = x__4; dbg = x__5 })" ] "(fun f__1 f__2 f__3 x__0 -> match x__0 with Simple x__1 -> f__1 x__1 | Prim (x__1, x__2, x__3, x__4) -> f__2 x__1 x__2 x__3 x__4 | Lookup_table { name = x__1; array_kind = x__2; element_kind = x__3; simples = x__4; dbg = x__5 } -> f__3 x__1 x__2 x__3 x__4 x__5)".
Definition named : Type := named_.
Extract Constant named => "| Simple of Simple.t | Prim of string * K.t * P.t * Debuginfo.t | Lookup_table of { name : string; array_kind : P.Array_kind.t; element_kind : KS.t; simples : Simple.t list; dbg : Debuginfo.t }".

(* 302 *)
Definition bound_simple (simple : Simple.t) : M named := ret (Simple simple).

(* 304 *)
Definition bound_prim (name : string) (kind : K.t) (prim : P.t)
    (dbg : Debuginfo.t) : M named :=
  ret (Prim name kind prim dbg).

(* 306-307. In the compiler: [name ~element_kind ~array_kind simples dbg]. *)
Definition bound_lookup_table (name : string) (element_kind : KS.t)
    (array_kind : P.Array_kind.t) (simples : list Simple.t)
    (dbg : Debuginfo.t) : M named :=
  ret (Lookup_table name array_kind element_kind simples dbg).

(* What [( let$ )], [return] and the functions between them answer when
   they have their first arguments: a function of [uacc
   ~shareable_constants ~typing_env_before_switch ~cse_before_switch
   ~local_cse]. The compiler has no name for this type. *)
Local Abbreviation rebuilder :=
  (UA.t -> Static_const.Map.t Symbol.t -> TE.t
   -> Common_subexpression_elimination.t
   -> Common_subexpression_elimination.t -> M (RE.t * UA.t)).

(* 309-388 *)
(* PORT-GAP(loose): 309, the binding operator [( let$ )] is the function
   [let_op_dollar]: where the compiler writes [let$ x = e in k], this file
   writes [let! tmp1 := e in let_op_dollar tmp1 (fun x => k)]. The function
   is a computation that answers the function of the five last arguments
   (in OCaml it does nothing before it has them all); so are [k] and
   [return]. 312 and 324, the attribute [@local] is not kept. *)
Definition let_op_dollar (expr : named) (k : Simple.t -> M rebuilder)
    : M rebuilder :=
  ret
    (fun uacc shareable_constants typing_env_before_switch cse_before_switch
         local_cse =>
      let* machine_width := TE.machine_width typing_env_before_switch in
      let& already_bound :=
        fun (simple : Simple.t) =>
        let! tmp1 := k simple in
        tmp1 uacc shareable_constants typing_env_before_switch
          cse_before_switch local_cse
      in
      match expr with
      | Simple simple => already_bound simple
      | Lookup_table name array_kind element_kind simples dbg =>
        (* 319-323 *)
        let* array_const :=
          let! tmp1 := UA.are_rebuilding_terms uacc in
          create_lookup_table_array_const dbg array_kind tmp1 simples
            machine_width
        in
        (* 324-346 *)
        let& create_lookup_table :=
          fun (static_const : option Static_const.t) =>
          let* symbol :=
            let! tmp1 := Current_unit.get_cu_exn tt in
            Symbol.manufacture tmp1 name
          in
          let* shareable_constants :=
            match static_const with
            | Some static_const =>
              (* 328: [when Static_const.can_share static_const] *)
              let! tmp1 := Static_const.can_share static_const in
              if tmp1
              then
                (* Note: this only enables sharing of identical arguments for
                   this switch -- the modified [shareable_constants] gets
                   thrown away. *)
                Static_const.Map.add static_const symbol shareable_constants
              else ret shareable_constants
            | None => ret shareable_constants
            end
          in
          let* fields :=
            let! tmp1 := KS.kind element_kind in
            let! tmp2 := papp1 T.alias_type_of tmp1 in
            List.map tmp2 simples
          in
          let* block_type :=
            T.immutable_array (Or_unknown_or_bottom.Ok element_kind) fields
              Alloc_mode.For_types.heap machine_width
          in
          let* uacc :=
            let! tmp1 :=
              LC.create_block_like symbol Variable_.Map.empty array_const
                typing_env_before_switch block_type
            in
            UA.add_lifted_constant uacc tmp1
          in
          let! tmp1 := Simple.symbol symbol in
          let! tmp2 := k tmp1 in
          tmp2 uacc shareable_constants typing_env_before_switch
            cse_before_switch local_cse
        in
        (* 347-355 *)
        let! tmp1 := RSC.to_const array_const in
        match tmp1 with
        | None =>
          (* Not rebuilding terms *)
          create_lookup_table None
        | Some (Flambda.Deleted_code | Flambda.Code _) =>
          fatal_error "Cannot bind code"
        | Some (Flambda.Static_const const) =>
          let! tmp1 := Static_const.Map.find_opt const shareable_constants in
          match tmp1 with
          | None => create_lookup_table (Some const)
          | Some symbol =>
            let! tmp1 := Simple.symbol symbol in
            already_bound tmp1
          end
        end
      | Prim name kind prim dbg =>
        (* 357-388 *)
        let! tmp1 := UA.required_names uacc in
        let! tmp2 :=
          find_cse_simple (Some false) cse_before_switch
            typing_env_before_switch tmp1 local_cse prim
        in
        match tmp2 with
        | Some simple => already_bound simple
        | None =>
          let* named := Named.create_prim prim dbg in
          let* var := Variable_.create None name kind in
          let* uacc :=
            let! tmp1 := NO.singleton_variable var NM.normal in
            UA.add_free_names uacc tmp1
          in
          let* local_cse :=
            let! tmp1 := P.Eligible_for_cse.create prim in
            match tmp1 with
            | None => ret local_cse
            | Some with_fixed_value =>
              let! tmp1 := TE.current_scope typing_env_before_switch in
              let! tmp2 := Simple.var var in
              Common_subexpression_elimination.add local_cse with_fixed_value
                tmp2 tmp1
            end
          in
          let* '(body, uacc) :=
            let! tmp1 := Simple.var var in
            let! tmp2 := k tmp1 in
            tmp2 uacc shareable_constants typing_env_before_switch
              cse_before_switch local_cse
          in
          let& duid := Flambda_debug_uid.none in
          let* machine_width :=
            let! tmp1 := UA.uenv uacc in
            UE.machine_width tmp1
          in
          let* binding :=
            (* PORT-GAP(record-order): 381-386, two fields of the inline
               record have a call: [simplified_defining_expr], the later
               field of the type, first; then [let_bound]. Each is bound
               before the record is built. *)
            let* simplified_defining_expr :=
              Simplified_named.create machine_width named
            in
            let* let_bound :=
              let! tmp1 := BV.create var duid NM.normal in
              BPt.singleton tmp1
            in
            ret
              (Simplified_named.Keep_binding let_bound
                 simplified_defining_expr None)
          in
          EB.make_new_let_bindings uacc [binding] body
        end
      end).

(* 390-394. [return] is a word of Rocq. In the compiler: [~added_code_size
   ~free_names expr uacc ~shareable_constants:_ ~typing_env_before_switch:_
   ~cse_before_switch:_ ~local_cse:_]. *)
Definition return_ (added_code_size : Code_size.t) (free_names : NO.t)
    (expr : RE.t) : M rebuilder :=
  ret
    (fun uacc (_ : Static_const.Map.t Symbol.t) (_ : TE.t)
         (_ _ : Common_subexpression_elimination.t) =>
      let* uacc := UA.notify_added added_code_size uacc in
      let* uacc := UA.add_free_names uacc free_names in
      ret (expr, uacc)).

(* 396-404 *)
Definition run (uacc : UA.t)
    (shareable_constants : Static_const.Map.t Symbol.t)
    (typing_env_before_switch : TE.t)
    (cse_before_switch : Common_subexpression_elimination.t) (k : rebuilder)
    : M (RE.t * UA.t) :=
  (* [local_cse] allows sharing between distinct arguments of the same switch.

     We can't update the CSE from the [dacc_before_switch] because that can bind
     to existing names that are not in the [required_names] and we can't use
     anymore. *)
  k uacc shareable_constants typing_env_before_switch cse_before_switch
    Common_subexpression_elimination.empty.

(* 406-408 *)
Inductive affine_immediate_kind : Type :=
| Tagged
| Naked.

(* 410-413 *)
Definition equal_affine_immediate_kind (kind1 kind2 : affine_immediate_kind)
    : M bool :=
  match kind1, kind2 with
  | Tagged, Tagged | Naked, Naked => ret true
  | (Tagged | Naked), _ => ret false
  end.

(* 415-417 *)
Definition affine_immediate_kind_to_standard_int (x : affine_immediate_kind)
    : M K.Standard_int.t :=
  match x with
  | Tagged => ret K.Standard_int.Tagged_immediate
  | Naked => ret K.Standard_int.Naked_immediate
  end.

(* 419-423 *)
Inductive affine_argument_of_mergeable_arm : Type :=
| Not_affine
| Maybe_affine
| Constant (_ : affine_immediate_kind) (_ : TI.t) (_ : TI.t)
  (** kind, input, output *)
| Affine (_ : affine_immediate_kind) (_ : TI.t) (_ : TI.t)
  (** kind, offset, slope *).

(* 425-433 *)
Definition recognize_affine_immediate_const (const : RWC.t)
    : M (option (affine_immediate_kind * TI.t)) :=
  let! tmp1 := Reg_width_const.descr const in
  match tmp1 with
  | Int_ids.Const.Descr.Naked_immediate naked_imm =>
    ret (Some (Naked, naked_imm))
  | Int_ids.Const.Descr.Tagged_immediate tagged_imm =>
    ret (Some (Tagged, tagged_imm))
  | Int_ids.Const.Descr.Naked_float32 _ | Int_ids.Const.Descr.Naked_float _
  | Int_ids.Const.Descr.Naked_int8 _ | Int_ids.Const.Descr.Naked_int16 _
  | Int_ids.Const.Descr.Naked_int32 _ | Int_ids.Const.Descr.Naked_int64 _
  | Int_ids.Const.Descr.Naked_nativeint _
  | Int_ids.Const.Descr.Naked_vec128 _ | Int_ids.Const.Descr.Naked_vec256 _
  | Int_ids.Const.Descr.Naked_vec512 _ | Int_ids.Const.Descr.Naked_mask _
  | Int_ids.Const.Descr.Null =>
    ret None
  | Int_ids.Const.Descr.Poison _ _ => ret None
  end.

(* 435-466. In the compiler: [~machine_width affine_argument discr const]. *)
(* PORT-GAP(loose): 436, the attribute [@local] is not kept. *)
Definition recognize_affine_argument
    (machine_width : Target_system.Machine_width.t)
    (affine_argument : affine_argument_of_mergeable_arm) (discr : TI.t)
    (const : RWC.t) : M affine_argument_of_mergeable_arm :=
  let& affine :=
    fun (kind : affine_immediate_kind) (offset slope : TI.t) =>
    ret (Affine kind offset slope)
  in
  (* PORT-GAP(loose): 437, the second of the two matched values is a call:
     it is bound to a name first. (Rocq would write a [let!] inside the
     branches of the match on the first value: the call would not be made
     when that value is [Not_affine].) *)
  let* recognized := recognize_affine_immediate_const const in
  match affine_argument, recognized with
  | Not_affine, _ | _, None => ret Not_affine
  | Maybe_affine, Some (kind, imm) => ret (Constant kind discr imm)
  | Constant kind arm arg, Some (imm_kind, imm) =>
    (let! tmp1 := equal_affine_immediate_kind kind imm_kind in
     if negb tmp1
     then fatal_error "Inconsistent kinds for mergeable switch argument"
     else ret tt) ;;
    let* arg_diff := TI.sub imm arg in
    let* arm_diff := TI.sub discr arm in
    (* CR-someday ncourant and bclement: this might fail to recognize affine
       relations in modular arithmetic, such as a switch: *)
    (*
     * 0 -> 0
     * 2 -> 0
     * 3 -> int_min
     *)
    (* which could be represented by [int_min * scrutinee], but is currently not
       recognized as affine because we compute [offset] and [slope] from the
       first two entries only. *)
    let! tmp1 := TI.mod_ arg_diff arm_diff in
    let! tmp2 := TI.zero machine_width in
    let! tmp3 := TI.equal tmp2 tmp1 in
    if tmp3
    then
      let* slope := TI.div arg_diff arm_diff in
      let* offset :=
        let! tmp1 := TI.mul slope arm in
        TI.sub arg tmp1
      in
      affine kind offset slope
    else ret Not_affine
  | Affine kind offset slope, Some (imm_kind, imm) =>
    (let! tmp1 := equal_affine_immediate_kind imm_kind kind in
     if negb tmp1
     then fatal_error "Inconsistent kinds for mergeable switch argument"
     else ret tt) ;;
    let! tmp1 := TI.mul discr slope in
    let! tmp2 := TI.add tmp1 offset in
    let! tmp3 := TI.equal imm tmp2 in
    if tmp3 then affine kind offset slope else ret Not_affine
  end.

(* 468-487 *)
(* PORT-GAP(type): [Affine_argument] and [Lookup_table_argument] have an
   inline record: their fields are taken by place, and the compiler's
   definition is the text that Rocq prints (without its comments). *)
Inductive mergeable_argument_ : Type :=
| Invariant_argument (_ : Simple.t)
| Tagged_scrutinee
| Not_scrutinee (* always tagged immediate *)
| Affine_argument (kind : affine_immediate_kind) (offset : TI.t)
    (slope : TI.t)
| Lookup_table_argument (array_kind : P.Array_kind.t)
    (array_load_kind : P.Array_load_kind.t) (first_discriminant : TI.t)
    (simples : list Simple.t)
  (** All arms are symbols or constants of the same [Flambda_kind.t]. For
      the value kind (with [array_kind = Values]), this variant allows a mix
      of symbols (including ones pointing at boxed numbers), tagged
      immediates and nulls; for all other kinds symbols are forbidden, so
      every arm is a constant of the kind described by [array_load_kind]. *).
Extract Inductive mergeable_argument_ => "mergeable_argument" [ "Invariant_argument" "Tagged_scrutinee" "Not_scrutinee" "(fun (x__1, x__2, x__3) -> Affine_argument { kind = x__1; offset = x__2; slope = x__3 })" "(fun (x__1, x__2, x__3, x__4) -> Lookup_table_argument { array_kind = x__1; array_load_kind = x__2; first_discriminant = x__3; simples = x__4 })" ] "(fun f__1 f__2 f__3 f__4 f__5 x__0 -> match x__0 with Invariant_argument x__1 -> f__1 x__1 | Tagged_scrutinee -> f__2 () | Not_scrutinee -> f__3 () | Affine_argument { kind = x__1; offset = x__2; slope = x__3 } -> f__4 x__1 x__2 x__3 | Lookup_table_argument { array_kind = x__1; array_load_kind = x__2; first_discriminant = x__3; simples = x__4 } -> f__5 x__1 x__2 x__3 x__4)".
Definition mergeable_argument : Type := mergeable_argument_.
Extract Constant mergeable_argument => "| Invariant_argument of Simple.t | Tagged_scrutinee | Not_scrutinee | Affine_argument of { kind : affine_immediate_kind; offset : TI.t; slope : TI.t } | Lookup_table_argument of { array_kind : P.Array_kind.t; array_load_kind : P.Array_load_kind.t; first_discriminant : TI.t; simples : Simple.t list }".

(* 489-494. In the compiler: [~num_arms] and a [function]. *)
Definition enough_arms (num_arms : int) (x : mergeable_argument) : M bool :=
  match x with
  | Invariant_argument _ | Tagged_scrutinee | Not_scrutinee => ret true
  | Affine_argument _ _ _ | Lookup_table_argument _ _ _ _ =>
    (* Only introduce affine computations and lookup tables if the switch is
       large enough *)
    ret (num_arms >=? i3)
  end.

(* 496-497 *)
Definition bound_tagged_scrutinee (scrutinee : Simple.t) (dbg : Debuginfo.t)
    : M named :=
  bound_prim "tagged_scrutinee" K.value (P.Unary P.Tag_immediate scrutinee)
    dbg.

(* 499-582. In the compiler: [~machine_width ~scrutinee mergeable_argument
   k]. Every [let$ x = e in k] of the compiler is [let! tmp1 := e in
   let_op_dollar tmp1 (fun x => k)]. *)
(* PORT-GAP(loose): 504, the attribute [@inline] is not kept; 552, the
   local module [ALK] is written out. *)
Definition rebuild_mergeable_argument
    (machine_width : Target_system.Machine_width.t) (scrutinee : Simple.t)
    (mergeable_argument : mergeable_argument) (k : Simple.t -> M rebuilder)
    : M rebuilder :=
  let& dbg := Debuginfo.none in
  match mergeable_argument with
  | Invariant_argument simple => k simple
  | Affine_argument kind offset slope =>
    (* 504-533 *)
    let& rebuild_affine_expr :=
      fun (scrutinee : Simple.t) (const : TI.t -> M RWC.t) =>
      let* standard_int := affine_immediate_kind_to_standard_int kind in
      let* kind := K.Standard_int.to_kind standard_int in
      let* '(must_negate, slope) :=
        let! tmp1 := TI.is_non_negative slope in
        if tmp1
        then ret (false, slope)
        else
          let! tmp2 := TI.neg slope in
          ret (true, tmp2)
      in
      (* 510-520 *)
      let! tmp1 :=
        let! tmp2 := TI.one machine_width in
        let! tmp3 := TI.equal slope tmp2 in
        if tmp3
        then bound_simple scrutinee
        else
          let! tmp4 := const slope in
          let! tmp5 := Simple.const tmp4 in
          bound_prim "scaled_arg" kind
            (P.Binary (P.Int_arith_ standard_int P.Mul) scrutinee tmp5)
            dbg
      in
      let_op_dollar tmp1 (fun scaled_arg =>
      (* 521-531 *)
      let! tmp1 :=
        let! tmp2 := TI.zero machine_width in
        let! tmp3 := TI.equal offset tmp2 in
        if tmp3 && negb must_negate
        then bound_simple scaled_arg
        else
          let! tmp4 := const offset in
          let! tmp5 := Simple.const tmp4 in
          bound_prim "final_arg" kind
            (P.Binary
               (P.Int_arith_ standard_int
                  (if must_negate then P.Sub else P.Add))
               tmp5 scaled_arg)
            dbg
      in
      let_op_dollar tmp1 (fun final_arg => k final_arg))
    in
    (* 534-538 *)
    match kind with
    | Naked => rebuild_affine_expr scrutinee RWC.naked_immediate
    | Tagged =>
      let! tmp1 := bound_tagged_scrutinee scrutinee dbg in
      let_op_dollar tmp1 (fun tagged_scrutinee =>
      rebuild_affine_expr tagged_scrutinee RWC.tagged_immediate)
    end
  | Tagged_scrutinee =>
    let! tmp1 := bound_tagged_scrutinee scrutinee dbg in
    let_op_dollar tmp1 (fun tagged_scrutinee => k tagged_scrutinee)
  | Not_scrutinee =>
    let! tmp1 := bound_tagged_scrutinee scrutinee dbg in
    let_op_dollar tmp1 (fun tagged_scrutinee =>
    let! tmp1 :=
      bound_prim "not_scrutinee" K.value
        (P.Unary P.Boolean_not tagged_scrutinee)
        dbg
    in
    let_op_dollar tmp1 (fun not_scrutinee => k not_scrutinee))
  | Lookup_table_argument array_kind array_load_kind first_discriminant
      simples =>
    (* 552-582 *)
    let* element_kind :=
      P.Array_load_kind.kind_of_loaded_value array_load_kind
    in
    let* loaded_kind := KS.kind element_kind in
    let! tmp1 :=
      bound_lookup_table "switch_block" element_kind array_kind simples dbg
    in
    let_op_dollar tmp1 (fun switch_block =>
    let! tmp1 :=
      bound_prim "tagged_scrutinee" K.value
        (P.Unary P.Tag_immediate scrutinee)
        dbg
    in
    let_op_dollar tmp1 (fun tagged_scrutinee =>
    let! tmp1 :=
      let! tmp2 := TI.zero machine_width in
      let! tmp3 := TI.equal first_discriminant tmp2 in
      if tmp3
      then bound_simple tagged_scrutinee
      else
        let! tmp4 := TI.neg first_discriminant in
        let! tmp5 := Simple.const_int tmp4 in
        bound_prim "offset_scrutinee" K.value
          (P.Binary (P.Int_arith_ K.Standard_int.Tagged_immediate P.Add)
             tagged_scrutinee tmp5)
          dbg
    in
    let_op_dollar tmp1 (fun offset_scrutinee =>
    let! tmp1 :=
      bound_prim "arg" loaded_kind
        (P.Binary
           (P.Array_load array_kind array_load_kind Mutability.Immutable)
           switch_block offset_scrutinee)
        dbg
    in
    let_op_dollar tmp1 (fun load_from_block => k load_from_block))))
  end.

(* 584 *)
(* PORT-GAP(verbatim): the exception is declared in the OCaml text at the
   head of the file. *)
Parameter Argument_cannot_be_used_in_lookup_table : exception unit.
Extract Inlined Constant Argument_cannot_be_used_in_lookup_table => "((fun () -> Argument_cannot_be_used_in_lookup_table), (function Argument_cannot_be_used_in_lookup_table -> Some () | _ -> None))".

(* 586-603 *)
Definition recognize_invariant_argument (required_names : Name.Set_.t)
    (arg : TI.Map.t alias_set) : M (option Simple.t) :=
  let* shared_alias_set :=
    TI.Map.fold
      ((fun _ alias_set shared_alias_set =>
         match shared_alias_set with
         | None => ret (Some alias_set)
         | Some shared_alias_set =>
           let! tmp1 := inter_alias_set alias_set shared_alias_set in
           ret (Some tmp1)
         end)
       : TI.t -> alias_set -> option alias_set -> M (option alias_set))
      arg None
  in
  let* shared_alias_set :=
    match shared_alias_set with
    | None =>
      (* This means that the argument is always poison. *)
      fatal_error "Trying to merge zero switch arms"
    | Some shared_alias_set => ret shared_alias_set
    end
  in
  filter_and_choose_alias required_names shared_alias_set.

(* 638-642 *)
(* PORT-GAP(loose): the compiler defines this type inside
   [recognize_mergeable_argument], in a local [open struct ... end]. *)
Inductive const_or_symbol : Type :=
| Const (_ : Reg_width_const.t)
| Symbol.

(* 605-757. In the compiler: [~machine_width ~scrutinee required_names ~dbg
   (arg : alias_set TI.Map.t)]. *)
(* PORT-GAP(loose): 608 and 624, the attribute [@local] is not kept; 650 and
   655, [raise_notrace] is written [raise]; 684 and 691, the two [when] are
   [if]s, by the rule of the guide. *)
Definition recognize_mergeable_argument
    (machine_width : Target_system.Machine_width.t) (scrutinee : Simple.t)
    (required_names : Name.Set_.t) (dbg : Debuginfo.t)
    (arg : TI.Map.t alias_set) : M (option mergeable_argument) :=
  (* 607-659 *)
  let& check_arm :=
    (fun discr alias_set pat =>
      let* '(affine_arg, args_rev_and_expected_discr) := ret pat in
      let& maybe_table_lookup_arg :=
        fun (constant_arg : affine_argument_of_mergeable_arm)
            (simple : Simple.t) =>
        (* These expressions can be compiled using lookup tables, which
           dramatically reduces code size. *)
        match args_rev_and_expected_discr with
        | None => ret (constant_arg, None)
        | Some (args_rev, expected_discr) =>
          let! tmp1 := TI.equal discr expected_discr in
          if negb tmp1
          then
            (* Discriminants must be d..(d + num_arms-1) (note that it is
               possible to have Switches that do not satisfy this criterion in
               Flambda2). *)
            ret (constant_arg, None)
          else
            let* expected_discr :=
              let! tmp1 := TI.one machine_width in
              TI.add tmp1 expected_discr
            in
            ret (constant_arg, Some (simple :: args_rev, expected_discr))
        end
      in
      let& maybe_constant_arg :=
        fun (const : RWC.t) =>
        let* constant_args :=
          recognize_affine_argument machine_width affine_arg discr const
        in
        let! tmp1 := Simple.const const in
        maybe_table_lookup_arg constant_args tmp1
      in
      match alias_set with
      | Poison kind =>
        let! tmp1 := RWC.const_poison kind "rebuild_switch" in
        let! tmp2 := Simple.const tmp1 in
        maybe_table_lookup_arg affine_arg tmp2
      | Aliases aliases =>
        let! tmp1 := Alias_set.find_best aliases in
        match tmp1 with
        | None => fatal_error "Unexpected empty argument"
        | Some simple =>
          (* The destination continuations must have constant or symbol
             arguments. 646-655: the arguments are in the order of the
             interface. *)
          let! tmp1 :=
            Simple.pattern_match' simple
              (fun _var (_ : Coercion.t) =>
                (* CR mshinwell: we could allow variables, if at toplevel *)
                (* Aliases should have been followed by now. *)
                raise_ Argument_cannot_be_used_in_lookup_table tt)
              (fun _ coercion =>
                (let! tmp2 := Coercion.free_names coercion in
                 let! tmp3 := NO.no_variables tmp2 in
                 if negb tmp3
                 then raise_ Argument_cannot_be_used_in_lookup_table tt
                 else ret tt) ;;
                ret Symbol)
              (fun const => ret (Const const))
          in
          match tmp1 with
          | Const const => maybe_constant_arg const
          | Symbol => maybe_table_lookup_arg Not_affine simple
          end
        end
      end)
    : TI.t -> alias_set
      -> affine_argument_of_mergeable_arm * option (list Simple.t * TI.t)
      -> M (affine_argument_of_mergeable_arm
            * option (list Simple.t * TI.t))
  in
  (* 660 *)
  let! tmp1 := recognize_invariant_argument required_names arg in
  match tmp1 with
  | Some simple => ret (Some (Invariant_argument simple))
  | None =>
    (* First discriminant is not necessarily zero, in which case the array
       lookup will be offset. *)
    let* first_discr :=
      try_with
        (fun _ =>
          let! tmp1 := TI.Map.min_binding arg in
          Stdlib_.fst tmp1)
        Not_found
        (fun _ => TI.zero machine_width)
    in
    (* 669-678 *)
    let& affine_is_identity :=
      fun (offset slope : TI.t) =>
      let! tmp1 := TI.zero machine_width in
      let! tmp2 := TI.equal offset tmp1 in
      and_then tmp2
        (let! tmp3 := TI.one machine_width in
         TI.equal slope tmp3)
    in
    let& affine_is_boolean_not :=
      fun (offset slope : TI.t) =>
      let! tmp1 := TI.one machine_width in
      let! tmp2 := TI.equal offset tmp1 in
      and_then tmp2
        (let! tmp3 := TI.minus_one machine_width in
         let! tmp4 := TI.equal slope tmp3 in
         and_then tmp4
           (let! tmp5 := TI.all_bools machine_width in
            let! tmp6 := TI.Map.of_set (fun _ => ret tt) tmp5 in
            TI.Map.subset_domain arg tmp6))
    in
    (* 679-757 *)
    match_exn
      (fun _ => TI.Map.fold check_arm arg (Maybe_affine, Some ([], first_discr)))
      Argument_cannot_be_used_in_lookup_table
      (fun _ => ret None)
      (fun x =>
        match x with
        | (Not_affine, None) => ret None
        | ((Maybe_affine | Constant _ _ _), _) =>
          fatal_error "Unexpected invariant argument"
        | (Affine kind offset slope, _) =>
          let! tmp1 := affine_is_identity offset slope in
          if tmp1
          then
            match kind with
            | Naked => ret (Some (Invariant_argument scrutinee))
            | Tagged => ret (Some Tagged_scrutinee)
            end
          else
            match kind with
            | Tagged =>
              let! tmp1 := affine_is_boolean_not offset slope in
              if tmp1
              then ret (Some Not_scrutinee)
              else ret (Some (Affine_argument kind offset slope))
            | Naked => ret (Some (Affine_argument kind offset slope))
            end
        | (Not_affine, Some ([], _)) => ret None
        | (Not_affine, Some (args_rev, _)) =>
          let* args := List.rev args_rev in
          (let! tmp1 := List.compare_length_with args 1 in
           assert_ (tmp1 >=? 0)) ;;
          (* Symbols are always of kind [value]; they may be freely mixed with
             [Const]s of kind [value] (i.e. tagged immediates). For all other
             kinds symbols are not permitted and every arm must be a constant
             of the same [Flambda_kind.t]. *)
          let& kind_of :=
            fun (simple : Simple.t) =>
            Simple.pattern_match' simple
              (fun _ (_ : Coercion.t) =>
                (* Variables have already been ruled out above. *)
                fatal_errorf4 "Variable (%a) was not expected here: %a"
                  Simple.print simple Debuginfo.print_compact dbg)
              (fun _ (_ : Coercion.t) => ret K.value)
              RWC.kind
          in
          let* first_kind :=
            let! tmp1 := List.hd args in
            kind_of tmp1
          in
          let! tmp1 :=
            List.for_all
              (fun arg =>
                let! tmp2 := kind_of arg in
                K.equal tmp2 first_kind)
              args
          in
          if negb tmp1
          then ret None
          else
            let& single_kind :=
              fun (array_kind : P.Array_kind.t)
                  (array_load_kind : P.Array_load_kind.t) =>
              ret
                (Some
                   (Lookup_table_argument array_kind array_load_kind
                      first_discr args))
            in
            match first_kind with
            | Flambda_kind.Value =>
              let! tmp1 :=
                List.for_all
                  (fun simple =>
                    let! tmp2 := Simple.must_be_const simple in
                    let! tmp3 := Option.bind tmp2 RWC.is_tagged_immediate in
                    Option.is_some tmp3)
                  args
              in
              if tmp1
              then
                single_kind P.Array_kind.Immediates
                  P.Array_load_kind.Immediates
              else
                (* It is possible that this array will contain only boxed floats
                   even with the float array optimization enabled. These would
                   not normally arise in the presence of such optimization, but
                   if we don't tell anyone it will be ok: we explicitly generate
                   the load using array load kind [Values] (which does not do
                   any float array optimization tests; all of those were
                   expanded in [Lambda_to_flambda]). *)
                single_kind P.Array_kind.Values P.Array_load_kind.Values
            | Flambda_kind.Naked_number nn =>
              match nn with
              | Flambda_kind.Naked_number_kind.Naked_immediate =>
                single_kind P.Array_kind.Naked_ints
                  P.Array_load_kind.Naked_ints
              | Flambda_kind.Naked_number_kind.Naked_float32 =>
                single_kind P.Array_kind.Naked_float32s
                  P.Array_load_kind.Naked_float32s
              | Flambda_kind.Naked_number_kind.Naked_float =>
                single_kind P.Array_kind.Naked_floats
                  P.Array_load_kind.Naked_floats
              | Flambda_kind.Naked_number_kind.Naked_int8 =>
                single_kind P.Array_kind.Naked_int8s
                  P.Array_load_kind.Naked_int8s
              | Flambda_kind.Naked_number_kind.Naked_int16 =>
                single_kind P.Array_kind.Naked_int16s
                  P.Array_load_kind.Naked_int16s
              | Flambda_kind.Naked_number_kind.Naked_int32 =>
                single_kind P.Array_kind.Naked_int32s
                  P.Array_load_kind.Naked_int32s
              | Flambda_kind.Naked_number_kind.Naked_int64 =>
                single_kind P.Array_kind.Naked_int64s
                  P.Array_load_kind.Naked_int64s
              | Flambda_kind.Naked_number_kind.Naked_nativeint =>
                single_kind P.Array_kind.Naked_nativeints
                  P.Array_load_kind.Naked_nativeints
              | Flambda_kind.Naked_number_kind.Naked_vec128 =>
                single_kind P.Array_kind.Naked_vec128s
                  P.Array_load_kind.Naked_vec128s
              | Flambda_kind.Naked_number_kind.Naked_vec256 =>
                single_kind P.Array_kind.Naked_vec256s
                  P.Array_load_kind.Naked_vec256s
              | Flambda_kind.Naked_number_kind.Naked_vec512 =>
                single_kind P.Array_kind.Naked_vec512s
                  P.Array_load_kind.Naked_vec512s
              | Flambda_kind.Naked_number_kind.Naked_mask =>
                single_kind P.Array_kind.Naked_masks
                  P.Array_load_kind.Naked_masks
              end
            | Flambda_kind.Region | Flambda_kind.Rec_info => ret None
            end
        end)
  end.

(* 759-846. In the compiler the first argument is the pattern of the
   record. *)
(* PORT-GAP(loose): 797, the attribute [@inline] is not kept. *)
Definition rebuild_switch (pat : Simplified_expr.simplified_switch_)
    (uacc : UA.t) (after_rebuild : Simplify_common.after_rebuild)
    : M (RE.t * UA.t) :=
  let* '{| Simplified_expr.arms := arms;
           Simplified_expr.condition_dbg := condition_dbg;
           Simplified_expr.scrutinee := scrutinee;
           Simplified_expr.scrutinee_ty := scrutinee_ty;
           Simplified_expr.shareable_constants := shareable_constants;
           Simplified_expr.typing_env_before_switch := typing_env_before_switch;
           Simplified_expr.cse_before_switch := cse_before_switch |} :=
    ret pat
  in
  let* machine_width := TE.machine_width typing_env_before_switch in
  (* 769-771 *)
  let* '(T3 new_let_conts arms mergeable_arms) :=
    TI.Map.fold (rebuild_arm uacc) arms (T3 [] TI.Map.empty No_arms)
  in
  let* num_arms := TI.Map.cardinal arms in
  (* 773-789 *)
  let* switch_merged :=
    match mergeable_arms with
    | No_arms | Not_mergeable => ret None
    | Mergeable cont args =>
      let* num_args := List.length args in
      let* mergeable_args :=
        let! tmp1 := UA.required_names uacc in
        List.filter_map
          (recognize_mergeable_argument machine_width scrutinee tmp1
             condition_dbg)
          args
      in
      let! tmp1 := List.compare_length_with mergeable_args num_args in
      let! tmp2 :=
        and_then (tmp1 =? 0)
          (List.for_all (enough_arms num_arms) mergeable_args)
      in
      if tmp2 then ret (Some (cont, mergeable_args)) else ret None
    end
  in
  (* 790-844 *)
  let* '(body, uacc) :=
    if num_arms <? 1
    then
      let* uacc := UA.notify_removed Removed_operations.branch uacc in
      let! tmp1 := RE.create_invalid Flambda.Invalid.Zero_switch_arms in
      ret (tmp1, uacc)
    else
      let& dbg := Debuginfo.none in
      let& normal_case :=
        fun (uacc : UA.t) =>
        (* In that case, even though some branches were removed by simplify we
           should not count them in the number of removed operations: these
           branches wouldn't have been taken during execution anyway. *)
        let* '(expr, uacc) :=
          EB.create_switch uacc condition_dbg scrutinee arms
        in
        (let! tmp1 := Flambda_features.check_invariants tt in
         let! tmp2 :=
           and_then tmp1
             (let! tmp3 := Simple.is_const scrutinee in
              ret (tmp3 && (num_arms >? 1)))
         in
         if tmp2
         then
           let! tmp3 := UA.are_rebuilding_terms uacc in
           let! tmp4 := papp1 RE.print tmp3 in
           fatal_errorf4
             "[Switch] with constant scrutinee (type: %a) should have been simplified away:@ %a"
             T.print scrutinee_ty tmp4 expr
         else ret tt) ;;
        ret (expr, uacc)
      in
      match switch_merged with
      | Some (dest, args) =>
        let* uacc := UA.notify_removed Removed_operations.branch uacc in
        (* CR bclement: should use a single unboxed product lookup table *)
        (* 822-839: the recursion is on the list. *)
        let rebuild_merged_switch :=
          fix rebuild_merged_switch
              (mergeable_args : list mergeable_argument)
              (args_rev : list Simple.t) {struct mergeable_args}
              : M rebuilder :=
            match mergeable_args with
            | [] =>
              let* args := List.rev args_rev in
              (* CR mshinwell: we could probably expose the actual integer
                 counts of continuations in [Name_occurrences] and then try to
                 inline out [dest]. This might happen anyway in the backend
                 though so this probably isn't that important for now. *)
              let* is_cold :=
                let! tmp1 := UA.uenv uacc in
                UE.is_cold_continuation tmp1 dest
              in
              let* apply_cont := Apply_cont.create None dest args dbg in
              (* 832-835: [return expr ~added_code_size ~free_names]; the
                 arguments are in the order of the definition. *)
              let! tmp1 := RE.create_apply_cont is_cold apply_cont in
              let! tmp2 := Apply_cont.free_names apply_cont in
              let! tmp3 := Code_size.apply_cont apply_cont in
              return_ tmp3 tmp2 tmp1
            | special_arg :: special_args =>
              rebuild_mergeable_argument machine_width scrutinee special_arg
                (fun arg =>
                  rebuild_merged_switch special_args (arg :: args_rev))
            end
        in
        let! tmp1 := rebuild_merged_switch args [] in
        run uacc shareable_constants typing_env_before_switch
          cse_before_switch tmp1
      | None => normal_case uacc
      end
  in
  (* 845-846 *)
  let* '(uacc, expr) := EB.bind_let_conts uacc body new_let_conts in
  after_rebuild expr uacc.

(* 848-887. In the compiler the second and the third argument are the
   patterns [(switch_arm, env_at_use)] and [(arms, dacc)]. *)
Definition simplify_arm (arm : TI.t) (pat : Switch_arm.t * TE.t)
    (pat0 : TI.Map.t SE.arms_tuple * DA.t)
    : M (TI.Map.t SE.arms_tuple * DA.t) :=
  let* '(switch_arm, env_at_use) := ret pat in
  let* '(arms, dacc) := ret pat0 in
  let* action := Switch_arm.action switch_arm in
  let* annotations := Switch_arm.annotations switch_arm in
  let* denv_at_use :=
    let! tmp1 := DA.denv dacc in
    DE.with_typing_env tmp1 env_at_use
  in
  let* args := AC.args action in
  let* use_kind :=
    Simplify_common.apply_cont_use_kind Simplify_common.Switch_branch action
  in
  let* '{| Simplify_simple.simples := args;
           Simplify_simple.simple_tys := arg_types |} :=
    let! tmp1 := DA.with_denv dacc denv_at_use in
    Simplify_simple.simplify_simples tmp1 args
  in
  let* denv_at_use :=
    let! tmp1 := Switch_arm.is_cold switch_arm in
    if tmp1 then DE.mark_as_cold denv_at_use else ret denv_at_use
  in
  (* 864-867 *)
  let* '(dacc, rewrite_id) :=
    let! tmp1 := AC.continuation action in
    DA.record_continuation_use dacc tmp1 use_kind denv_at_use arg_types
  in
  (* 868-872: [a |> f] is [f a] *)
  let* arity :=
    let! tmp1 :=
      List.map
        (fun ty =>
          let! tmp2 := T.kind ty in
          K.With_subkind.anything tmp2)
        arg_types
    in
    Flambda_arity.create_singletons tmp1
  in
  let* action := Apply_cont.update_args action args in
  let* dbg := AC.debuginfo action in
  let* dbg :=
    let! tmp1 := DA.denv dacc in
    DE.add_inlined_debuginfo tmp1 dbg
  in
  let* action := AC.with_debuginfo action dbg in
  (* 877-883 *)
  let* dacc :=
    let! tmp1 := Apply_cont.continuation action in
    let! tmp2 := papp3 Flow.Acc.add_apply_cont_args rewrite_id tmp1 args in
    DA.map_flow_acc dacc tmp2
  in
  let* arms :=
    TI.Map.add arm
      (SE.Arms_tuple action annotations rewrite_id arity env_at_use)
      arms
  in
  ret (arms, dacc).

(* PORT-GAP(decl): the float [0.] of line 1012. *)
Parameter float_0 : Stdlib_.float_.
Extract Inlined Constant float_0 => "0.".

(* PORT-GAP(type): 956-992, the value [join_analysis_result] of
   [decide_continuation_specialization0] is of a type of polymorphic
   variants, which the compiler does not name: a Rocq type whose
   constructors are printed as the compiler's tags. Four of the tags are
   also tags of the answer of the function (below): here their names have
   one [_]. *)
Inductive join_analysis_result : Type :=
| Not_enough_join_info_
| No_reason_to_spec_
| Spec (_ : T.Join_analysis.t Apply_cont_rewrite_id.t)
    (_ _ : Apply_cont_rewrite_id.Set_.t)
| All_unknown_
| Too_many_unknown_uses_.
Extract Inductive join_analysis_result => "[ `Not_enough_join_info | `No_reason_to_spec | `Spec of Apply_cont_rewrite_id.t Flambda2_types.Join_analysis.t * Apply_cont_rewrite_id.Set.t * Apply_cont_rewrite_id.Set.t | `All_unknown | `Too_many_unknown_uses ]" [ "`Not_enough_join_info" "`No_reason_to_spec" "`Spec" "`All_unknown" "`Too_many_unknown_uses" ].

(* PORT-GAP(type): the answer of [decide_continuation_specialization0] and
   of [decide_continuation_specialization] is of a type of polymorphic
   variants, which the compiler does not name: a Rocq type whose
   constructors are printed as the compiler's tags (in the order of the
   match of lines 1023-1038). *)
Inductive continuation_specialization : Type :=
| Disabled
| Single_use
| Exn_handler
| Toplevel
| All_unknown
| No_reason_to_spec
| Not_lifting
| Cannot_specialize
| Insufficient_lifting_budget
| Not_enough_join_info
| Too_many_unknown_uses
| Too_costly
| Specialized (_ : Continuation.t) (_ : int).
Extract Inductive continuation_specialization => "[ `Disabled | `Single_use | `Exn_handler | `Toplevel | `All_unknown | `No_reason_to_spec | `Not_lifting | `Cannot_specialize | `Insufficient_lifting_budget | `Not_enough_join_info | `Too_many_unknown_uses | `Too_costly | `Specialized of Continuation.t * int ]" [ "`Disabled" "`Single_use" "`Exn_handler" "`Toplevel" "`All_unknown" "`No_reason_to_spec" "`Not_lifting" "`Cannot_specialize" "`Insufficient_lifting_budget" "`Not_enough_join_info" "`Too_many_unknown_uses" "`Too_costly" "`Specialized" ].

(* 889-1015. In the compiler: [~dacc ~switch ~scrutinee]. *)
(* PORT-GAP(loose): 983-988, the match on the integers 0 and 1 is an [if]
   on a named value; 990-993, the cases [... as res -> res] are written one
   by one. *)
Definition decide_continuation_specialization0 (dacc : DA.t)
    (switch : Switch.t) (scrutinee : Simple.t)
    : M continuation_specialization :=
  let! tmp1 := DA.are_lifting_conts dacc in
  match tmp1 with
  | Are_lifting_conts.Lifting_out_of _ =>
    fatal_errorf0
      "[Are_lifting_cont] values in the dacc cannot be [Lifting_out_of _] when going downwards through a [Switch] expression. See the explanation in [are_lifting_conts.mli]."
  | Are_lifting_conts.Not_lifting _ => ret Not_lifting
  | Are_lifting_conts.Analyzing continuation is_exn_handler uses =>
    (* Some preliminary requirements. We do **not** specialize continuations if
       one of the following conditions are true:

       - they have only one (or less) use

       - they are an exception handler. To handle this case, the existing
       mechanism used to rewrite specialized calls on the way up should be
       extended to also rewrite pop_traps and other uses of exn handlers (which
       is not currently the case).

       - we are at toplevel, in which case there can be symbols which we might
       duplicate by specializing (which would be an error). More generally, the
       benefits of specialization at unit toplevel do not seem that great,
       because partial evaluation would be better. *)
    let* n_uses := Continuation_uses.number_of_uses uses in
    if n_uses <=? 1
    then ret Single_use
    else if is_exn_handler
    then ret Exn_handler
    else
      let! tmp1 := DA.denv dacc in
      let! tmp2 := DE.at_unit_toplevel tmp1 in
      if tmp2
      then ret Toplevel
      else
        let* denv := DA.denv dacc in
        let! tmp1 := DE.specialization_cost denv in
        match tmp1 with
        | Specialization_cost.Cannot_specialize reason =>
          (* CR gbury: we could try and emit something analog to the inlining
             report, but for other optimizations at one point ? *)
          match reason with
          | Specialization_cost.Specialization_disabled => ret Disabled
          | Specialization_cost.At_toplevel => ret Toplevel
          | Specialization_cost.Contains_static_consts
          | Specialization_cost.Contains_set_of_closures =>
            ret Cannot_specialize
          end
        | Specialization_cost.Can_specialize spec_cost =>
          (* We should never reach here if specialization is disabled, since we
             should never have created a `Can_specialize` value for the
             specialization_cost *)
          (let! tmp1 := Flambda_features.match_in_match tt in
           if negb tmp1
           then
             fatal_errorf0
               "Cannot specialize continuations (due to command line arguments), this code path should not have been reached."
           else ret tt) ;;
          (* Estimate the cost of lifting: this mainly comes from adding new
             parameters, which increase the work done by the typing env, as well
             as the flow analysis. We then only do the lifting if the cost is
             within the budget for the current function. *)
          let* lifting_budget := DA.get_continuation_lifting_budget dacc in
          let* lifting_cost :=
            DE.cost_of_lifting_continuations_out_of_current_one denv
          in
          (* is_lifting_allowed_by_budget ? *)
          if negb ((lifting_budget >? 0) && (lifting_cost <=? lifting_budget))
          then ret Insufficient_lifting_budget
          else
            (* Main Criterion: whether all callsites (but one) of the
               continuation determine the value of the scrutinee (and therefore
               the specialized versions will eliminate the switch in favor of
               an apply_cont directly). *)
            let* join_analysis_result :=
              let! tmp1 := DE.join_analysis denv in
              match tmp1 with
              | None => ret Not_enough_join_info_
              | Some join_analysis =>
                let! tmp1 := DE.typing_env denv in
                let! tmp2 :=
                  T.Join_analysis.simple_refined_at_join join_analysis tmp1
                    scrutinee
                in
                match tmp2 with
                | T.Join_analysis.Not_refined_at_join =>
                  ret Not_enough_join_info_
                | T.Join_analysis.Invariant_in_all_uses _ =>
                  (* in this case, we don't need to specialize to know the
                     scrutinee, or to simplify the switch, it will happen
                     without specialization. *)
                  ret No_reason_to_spec_
                | T.Join_analysis.Variable_refined_at_these_uses var_analysis =>
                  let* '(specialized, generic) :=
                    T.Join_analysis.Variable_refined_at_join.fold_values_at_uses
                      (fun id value pat =>
                        let* '(specialized, generic) := ret pat in
                        match value with
                        | Or_unknown.Known _ =>
                          let! tmp1 :=
                            Apply_cont_rewrite_id.Set_.add id specialized
                          in
                          ret (tmp1, generic)
                        | Or_unknown.Unknown =>
                          let! tmp1 :=
                            Apply_cont_rewrite_id.Set_.add id generic
                          in
                          ret (specialized, tmp1)
                        end)
                      var_analysis
                      (Apply_cont_rewrite_id.Set_.empty,
                       Apply_cont_rewrite_id.Set_.empty)
                  in
                  let* n := Apply_cont_rewrite_id.Set_.cardinal generic in
                  if (n =? 0) || (n =? 1)
                  then ret (Spec join_analysis specialized generic)
                  else
                    let! tmp1 :=
                      Apply_cont_rewrite_id.Set_.is_empty specialized
                    in
                    if tmp1
                    then ret All_unknown_
                    else ret Too_many_unknown_uses_
                end
              end
            in
            match join_analysis_result with
            | No_reason_to_spec_ => ret No_reason_to_spec
            | Too_many_unknown_uses_ => ret Too_many_unknown_uses
            | All_unknown_ => ret All_unknown
            | Not_enough_join_info_ => ret Not_enough_join_info
            | Spec join_analysis specialized generic =>
              (* Specialization benefit estimation: we use heuristics similar
                 to that of inlining to estimate the benefit based on code size
                 and removed operations (note that we use the join info in the
                 typing env to estimate which operations will be removed during
                 specialization, rather that computing it speculatively like is
                 done for inlining). *)
              let* cost_metrics :=
                let! tmp1 := DE.typing_env denv in
                Specialization_cost.cost_metrics tmp1 switch join_analysis
                  specialized generic spec_cost
              in
              let* final_cost :=
                let! tmp1 := DE.inlining_arguments denv in
                Cost_metrics.evaluate tmp1 cost_metrics
              in
              let* threshold :=
                Flambda_features.Expert.cont_spec_threshold tt
              in
              let! tmp1 := Float.compare threshold float_0 in
              let! tmp2 :=
                or_else (tmp1 <? 0)
                  (let! tmp3 := Float.compare final_cost threshold in
                   ret (tmp3 >? 0))
              in
              if tmp2
              then ret Too_costly
              else ret (Specialized continuation lifting_cost)
            end
        end
  end.

(* 1017-1038. [Profile.record_with_counters ~accumulate:true name f ()
   ~counter_f]: the arguments are in the order of the interface. *)
Definition decide_continuation_specialization (dacc : DA.t)
    (switch : Switch.t) (scrutinee : Simple.t)
    : M continuation_specialization :=
  Profile.record_with_counters (Some true)
    (fun result =>
      let* counters := Profile.Counters.create tt in
      match result with
      | Disabled => ret counters
      | Single_use => ret counters
      | Exn_handler => ret counters
      | Toplevel => ret counters
      | All_unknown => Profile.Counters.incr "all_unknown" counters
      | No_reason_to_spec => Profile.Counters.incr "no_reason" counters
      | Not_lifting => Profile.Counters.incr "not_lifting" counters
      | Cannot_specialize => Profile.Counters.incr "cannot_spec" counters
      | Insufficient_lifting_budget =>
        Profile.Counters.incr "no_lifting_budget" counters
      | Not_enough_join_info => Profile.Counters.incr "no_join_info" counters
      | Too_many_unknown_uses =>
        Profile.Counters.incr "too_much_unknown" counters
      | Too_costly => Profile.Counters.incr "not_beneficial" counters
      | Specialized _ _ => Profile.Counters.incr "specialized" counters
      end)
    "continuation_specialization"
    (fun (_ : unit) =>
      decide_continuation_specialization0 dacc switch scrutinee)
    tt.

(* 1040-1096 *)
Definition simplify_switch (dacc : DA.t) (switch : Switch.t)
    (down_to_up : Simplify_common.down_to_up SE.t) : M (SE.t * DA.t) :=
  let* scrutinee := Switch.scrutinee switch in
  let* '(scrutinee_ty, scrutinee) :=
    S.simplify_simple dacc scrutinee NM.normal
  in
  let& dacc_before_switch := dacc in
  let* typing_env_at_use := DA.typing_env dacc in
  (* 1047-1055 *)
  let* arms :=
    let! tmp1 := Switch.arms switch in
    TI.Map.filter_map
      (fun arm action =>
        let* shape := T.this_naked_immediate arm in
        let! tmp2 := T.meet typing_env_at_use scrutinee_ty shape in
        match tmp2 with
        | Or_bottom.Bottom => ret None
        | Or_bottom.Ok (_meet_ty, env_at_use) =>
          ret (Some (action, env_at_use))
        end)
      tmp1
  in
  let! tmp1 := TI.Map.get_singleton arms in
  match tmp1 with
  | Some (_, (arm, env_at_use)) =>
    (* Rewrite to a regular apply_cont so that it is an inlinable use. *)
    let* denv_at_use :=
      let! tmp1 := DA.denv dacc in
      DE.with_typing_env tmp1 env_at_use
    in
    let* dacc := DA.with_denv dacc denv_at_use in
    let! tmp1 := Switch_arm.action arm in
    Simplify_apply_cont_expr.simplify_apply_cont dacc tmp1
      (fun dacc simplified_expr =>
        let! tmp2 :=
          SE.notify_removed Removed_operations.branch simplified_expr
        in
        down_to_up dacc tmp2)
  | None =>
    let* '(arms, dacc) :=
      TI.Map.fold simplify_arm arms (TI.Map.empty, dacc)
    in
    (* 1068-1075 *)
    let* dacc :=
      let! tmp1 := TI.Map.cardinal arms in
      if tmp1 <=? 1
      then ret dacc
      else
        let! tmp2 := Simple.free_names scrutinee in
        let! tmp3 := papp1 Flow.Acc.add_used_in_current_handler tmp2 in
        DA.map_flow_acc dacc tmp3
    in
    let* condition_dbg :=
      let! tmp1 := Switch.condition_dbg switch in
      let! tmp2 := DA.denv dacc in
      DE.add_inlined_debuginfo tmp2 tmp1
    in
    (* 1079-1090 *)
    let* dacc :=
      let! tmp1 := decide_continuation_specialization dacc switch scrutinee in
      match tmp1 with
      | Specialized continuation lifting_cost =>
        let* dacc :=
          DA.decrease_continuation_lifting_budget dacc lifting_cost
        in
        let* dacc :=
          let! tmp1 :=
            Are_lifting_conts.lift_continuations_out_of continuation
          in
          DA.with_are_lifting_conts dacc tmp1
        in
        let* dacc := DA.add_continuation_to_specialize dacc continuation in
        ret dacc
      | _ => ret dacc
      end
    in
    let* shareable_constants := DA.shareable_constants dacc_before_switch in
    let* typing_env_before_switch := DA.typing_env dacc_before_switch in
    let* cse_before_switch :=
      let! tmp1 := DA.denv dacc_before_switch in
      DE.cse tmp1
    in
    let! tmp1 :=
      SE.simplified_switch arms condition_dbg scrutinee scrutinee_ty
        shareable_constants typing_env_before_switch cse_before_switch
    in
    down_to_up dacc tmp1
  end.
