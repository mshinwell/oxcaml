(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*    Pierre Chambart and Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2021--2021 OCamlPro SAS                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows middle_end/flambda2/simplify/flow/flow_types.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, module by module and
   function by function under the compiler's names; the numbers in the
   comments are the lines of that file. What is not from that file: the form
   (the monad, the temporaries [tmpN] and their order) is that of GUIDE.md;
   the two types that Rocq cannot print itself keep the compiler's text in
   a directive of the extraction. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Alloc_mode Apply_cont_rewrite_id
  Bound_parameters Code_id Continuation Continuation_callsite_map
  Continuation_extra_params_and_args Flambda_kind Flambda_primitive Format
  Lifted_constant_state List Mutability Name Name_occurrences Named_rewrite
  Named_rewrite_id Numeric_types Or_unknown Simple Value_slot Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* CR chambart/gbury: we might want to also track function_slots in addition to
   value_slots. *)

(* CR-someday chambart/gbury: get rid of Name_occurences everywhere, this is not
   small while we need only the names

   mshinwell: in practice I'm not sure this will make any difference *)

(* Continuation arguments at call sites of continuations *)
(* ***************************************************** *)

(* 26-37 *)
Module Cont_arg.
  (* 27-30 *)
  Inductive t : Type :=
    | Function_result
    | Simple (_ : Simple.t)
    | New_let_binding (_ : Variable_.t) (_ : Name_occurrences.t).

  (* 32-36: the compiler's function is a [function] of its second
     argument. *)
  Definition print (ppf : Format.formatter) (x : Cont_arg.t) : M unit :=
    match x with
    | Function_result => Format.fprintf0 ppf "Function_result"
    | Simple s => Simple.print ppf s
    | New_let_binding v _ =>
      Format.fprintf2 ppf "New_let_binding %a" Variable_.print v
    end.
End Cont_arg.

(* Primitives that we must track for mutable unboxing *)
(* ************************************************** *)

(* 42-75 *)
Module Mutable_prim.
  (* PORT-GAP(type): 43-63, a variant with inline records: in Rocq the
     fields are by place, as in decl/Flow_types.v; the extracted file has
     the compiler's definition, which the directive of [t] holds. *)
  Inductive t_ : Type :=
    | Is_int (_ : Variable_.t)
    | Get_tag (_ : Variable_.t)
    | Block_load (bak : Flambda_primitive.Block_access_kind.t)
        (mut : Mutability.t) (block : Variable_.t) (field : int)
    | Block_set (bak : Flambda_primitive.Block_access_kind.t)
        (block : Variable_.t) (field : int) (value : Simple.t)
    | Make_block (kind : Flambda_primitive.Block_kind.t) (mut : Mutability.t)
        (alloc_mode : Alloc_mode.For_allocations.t) (fields : list Simple.t).
  Extract Inductive t_ => "t"
    [ "Is_int" "Get_tag"
      "(fun (x__1, x__2, x__3, x__4) -> Block_load { bak = x__1; mut = x__2; block = x__3; field = x__4 })"
      "(fun (x__1, x__2, x__3, x__4) -> Block_set { bak = x__1; block = x__2; field = x__3; value = x__4 })"
      "(fun (x__1, x__2, x__3, x__4) -> Make_block { kind = x__1; mut = x__2; alloc_mode = x__3; fields = x__4 })" ]
    "(fun f__1 f__2 f__3 f__4 f__5 x__0 -> match x__0 with Is_int x__1 -> f__1 x__1 | Get_tag x__1 -> f__2 x__1 | Block_load { bak = x__1; mut = x__2; block = x__3; field = x__4 } -> f__3 x__1 x__2 x__3 x__4 | Block_set { bak = x__1; block = x__2; field = x__3; value = x__4 } -> f__4 x__1 x__2 x__3 x__4 | Make_block { kind = x__1; mut = x__2; alloc_mode = x__3; fields = x__4 } -> f__5 x__1 x__2 x__3 x__4)".
  Definition t : Type := t_.
  Extract Constant t => "
    | Is_int of Variable.t
    | Get_tag of Variable.t
    | Block_load of
        { bak : Flambda_primitive.Block_access_kind.t;
          mut : Mutability.t;
          block : Variable.t;
          field : int
        }
    | Block_set of
        { bak : Flambda_primitive.Block_access_kind.t;
          block : Variable.t;
          field : int;
          value : Simple.t
        }
    | Make_block of
        { kind : Flambda_primitive.Block_kind.t;
          mut : Mutability.t;
          alloc_mode : Alloc_mode.For_allocations.t;
          fields : Simple.t list
        }".

  (* 65-74: the compiler's function is a [function] of its second
     argument. *)
  Definition print (ppf : Format.formatter) (x : Mutable_prim.t) : M unit :=
    match x with
    | Is_int v => Format.fprintf2 ppf "Is_int (%a)" Variable_.print v
    | Get_tag v => Format.fprintf2 ppf "Get_tag (%a)" Variable_.print v
    | Block_load _ _ block field =>
      Format.fprintf3 ppf "Block_load (%a, %i)" Variable_.print block field
    | Block_set _ block field value =>
      Format.fprintf5 ppf "Block_set (%a, %i, %a)" Variable_.print block field
        Simple.print value
    | Make_block _ _ _ fields =>
      Format.fprintf2 ppf "Make_block [%a]" Simple.List.print fields
    end.
End Mutable_prim.

(* Bindings to primitive that we track for the mutable unboxing *)
(* ************************************************************ *)

(* 80-100 *)
Module Mutable_let_prim.
  (* 81-86 *)
  Record t : Type :=
    { bound_var : Variable_.t;
      prim : Mutable_prim.t;
      original_prim : Flambda_primitive.t;
      named_rewrite_id : Named_rewrite_id.t
    }.

  (* 88-90. The compiler's second parameter is the pattern
     [{ bound_var; prim; original_prim = _; named_rewrite_id = _ }]. *)
  Definition print (ppf : Format.formatter) (t : Mutable_let_prim.t)
      : M unit :=
    let* '{| Mutable_let_prim.bound_var := bound_var;
             Mutable_let_prim.prim := prim;
             Mutable_let_prim.original_prim := _;
             Mutable_let_prim.named_rewrite_id := _
          |} :=
      ret t
    in
    Format.fprintf4 ppf "%a = %a" Variable_.print bound_var Mutable_prim.print
      prim.

  (* 92-99 *)
  Module List.
    (* 93: [type nonrec t = t list] *)
    Definition t : Type := list Mutable_let_prim.t.

    (* 95-98 *)
    Definition print_rev (ppf : Format.formatter) (l : Mutable_let_prim.List.t)
        : M unit :=
      let! tmp1 := decl.List.rev l in
      let! tmp2 :=
        papp2 Format.pp_print_list (Some Format.pp_print_space) print
      in
      Format.fprintf2 ppf "[%a]" tmp2 tmp1.
  End List.
End Mutable_let_prim.

(* Accumulated flow information for a single continuation handler *)
(* ************************************************************** *)

(* 105-186 *)
Module Continuation_info.
  (* Some notes:

     - {direct_aliases} is used to have a more precise escaping analysis for
     mutable unboxing, since from_lambda occasionally generates aliases of the
     form [let r' = r], which without a precise alias tracking, would be
     considered as escaping.

     - the {bindings} field records dependencies between names, usually created
     by primitive applications; in the case of effectful primitives (that can't
     be removed), we do not record dependencies, but instead recrod all args of
     the effectful prim as unconditionally used (in {used_in_handler}).
     Similarly, for primitives tracked in {mutable_let_prims_rev}, we do not
     record the dependencies in this field, since we already have the more
     precise information. *)
  (* 120-135 *)
  Record t : Type :=
    { continuation : Continuation.t;
      recursive : bool;
      is_exn_handler : bool;
      params : Bound_parameters.t;
      parent_continuation : option Continuation.t;
      used_in_handler : Name_occurrences.t;
      bindings : Name.Map.t Name_occurrences.t;
      direct_aliases : Variable_.Map.t Simple.t;
      mutable_let_prims_rev : Mutable_let_prim.List.t;
      defined : Variable_.Set_.t;
      code_ids : Code_id.Map.t Name_occurrences.t;
      value_slots : Value_slot.Map.t (Name.Map.t Name_occurrences.t);
      apply_cont_args :
        Continuation_callsite_map.t (Numeric_types.Int.Map.t Cont_arg.t)
    }.

  (* 137-185. The compiler's second parameter is the pattern of all the
     fields. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Continuation_info.t)
      : M unit :=
    let* '{| Continuation_info.continuation := continuation;
             Continuation_info.recursive := recursive;
             Continuation_info.is_exn_handler := is_exn_handler;
             Continuation_info.params := params;
             Continuation_info.parent_continuation := parent_continuation;
             Continuation_info.used_in_handler := used_in_handler;
             Continuation_info.bindings := bindings;
             Continuation_info.direct_aliases := direct_aliases;
             Continuation_info.mutable_let_prims_rev := mutable_let_prims_rev;
             Continuation_info.defined := defined;
             Continuation_info.code_ids := code_ids;
             Continuation_info.value_slots := value_slots;
             Continuation_info.apply_cont_args := apply_cont_args
          |} :=
      ret t
    in
    (* 171-184 *)
    let! tmp1 := papp1 Numeric_types.Int.Map.print Cont_arg.print in
    let! tmp2 := papp1 Apply_cont_rewrite_id.Map.print tmp1 in
    let! tmp3 := papp1 Continuation.Map.print tmp2 in
    let! tmp4 := papp1 Name.Map.print Name_occurrences.print in
    let! tmp5 := papp1 Value_slot.Map.print tmp4 in
    let! tmp6 := papp1 Code_id.Map.print Name_occurrences.print in
    let! tmp7 := papp1 Variable_.Map.print Simple.print in
    let! tmp8 := papp1 Name.Map.print Name_occurrences.print in
    let! tmp9 :=
      papp2 Format.pp_print_option
        (Some (fun ppf (_ : unit) => Format.fprintf0 ppf "root"))
        Continuation.print
    in
    Format.fprintf24 ppf
      "@[<hov 1>(@[<hov 1>(continuation %a)@]@ %s%s@[<hov 1>(params %a)@]@ @[<hov 1>(parent_continuation %a)@]@ @[<hov 1>(used_in_handler %a)@]@ @[<hov 1>(bindings %a)@]@ @[<hov 1>(direct_aliases %a)@]@ @[<hov 1>(ref_prims %a)@]@ @[<hov 1>(defined %a)@]@ @[<hov 1>(code_ids %a)@]@ @[<hov 1>(value_slots %a)@]@ @[<hov 1>(apply_cont_args %a)@])@]"
      Continuation.print continuation
      (if recursive then "(recursive) " else "")
      (if is_exn_handler then "(exn_handler) " else "")
      Bound_parameters.print params
      tmp9 parent_continuation
      Name_occurrences.print used_in_handler
      tmp8 bindings
      tmp7 direct_aliases
      Mutable_let_prim.List.print_rev mutable_let_prims_rev
      Variable_.Set_.print
      defined
      tmp6
      code_ids
      tmp5
      value_slots
      tmp3
      apply_cont_args.
End Continuation_info.

(* Flow accumulator *)
(* **************** *)

(* 191-224 *)
Module Acc.
  (* 192-198 *)
  Record t : Type :=
    { stack : list Continuation_info.t;
      map : Continuation.Map.t Continuation_info.t;
      extra : Continuation.Map.t Continuation_extra_params_and_args.t;
      lifted_constants : Lifted_constant_state.t;
      dummy_toplevel_cont : Continuation.t
    }.

  (* 200-204 *)
  Definition print_stack (ppf : Format.formatter)
      (stack : list Continuation_info.t) : M unit :=
    let! tmp1 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space)
        Continuation_info.print
    in
    Format.fprintf2 ppf "@[<v 1>(%a)@]" tmp1 stack.

  (* 206 *)
  Definition print_map (ppf : Format.formatter)
      (map : Continuation.Map.t Continuation_info.t) : M unit :=
    Continuation.Map.print Continuation_info.print ppf map.

  (* 208-209 *)
  Definition print_extra (ppf : Format.formatter)
      (extra : Continuation.Map.t Continuation_extra_params_and_args.t)
      : M unit :=
    Continuation.Map.print Continuation_extra_params_and_args.print ppf extra.

  (* 211-223. The compiler's second parameter is the pattern
     [{ stack; map; extra; lifted_constants; dummy_toplevel_cont = _ }]. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Acc.t) : M unit :=
    let* '{| Acc.stack := stack;
             Acc.map := map;
             Acc.extra := extra;
             Acc.lifted_constants := lifted_constants;
             Acc.dummy_toplevel_cont := _
          |} :=
      ret t
    in
    Format.fprintf8 ppf
      "@[<hov 1>(@[<hov 1>(stack %a)@]@ @[<hov 1>(map %a)@]@ @[<hov 1>(extra %a)@]@ @[<hov 1>(lifted_constants %a)@])@]"
      print_stack stack
      print_map map
      print_extra extra
      Lifted_constant_state.print lifted_constants.
End Acc.

(* Result of the flow analysis: reachable code ids *)
(* *********************************************** *)

(* 229-242 *)
Module Reachable_code_ids.
  (* 230-233 *)
  Record t : Type :=
    { live_code_ids : Code_id.Set_.t;
      ancestors_of_live_code_ids : Code_id.Set_.t
    }.

  (* 235-241. The compiler's second parameter is the pattern
     [{ live_code_ids; ancestors_of_live_code_ids; }]. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Reachable_code_ids.t)
      : M unit :=
    let* '{| Reachable_code_ids.live_code_ids := live_code_ids;
             Reachable_code_ids.ancestors_of_live_code_ids :=
               ancestors_of_live_code_ids
          |} :=
      ret t
    in
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(live_code_ids@ %a)@]@ @[<hov 1>(ancestors_of_live_code_ids@ %a)@])@]"
      Code_id.Set_.print live_code_ids
      Code_id.Set_.print ancestors_of_live_code_ids.
End Reachable_code_ids.

(* Result of the flow analysis: data flow analysis *)
(* *********************************************** *)

(* 247-262 *)
Module Data_flow_result.
  (* 248-251 *)
  Record t : Type :=
    { required_names : Name.Set_.t;
      reachable_code_ids : Or_unknown.t Reachable_code_ids.t
    }.

  (* 253-261. The compiler's second parameter is the pattern
     [{ required_names; reachable_code_ids; }]. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Data_flow_result.t)
      : M unit :=
    let* '{| Data_flow_result.required_names := required_names;
             Data_flow_result.reachable_code_ids := reachable_code_ids
          |} :=
      ret t
    in
    let! tmp1 := papp1 Or_unknown.print Reachable_code_ids.print in
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(required_names@ %a)@]@ @[<hov 1>(reachable_code_ids@ %a)@]@ )@]"
      Name.Set_.print required_names
      tmp1 reachable_code_ids.
End Data_flow_result.

(* Result of the flow analysis: aliased parameters of continuations *)
(* **************************************************************** *)

(* 267-298 *)
Module Continuation_param_aliases.
  (* 268-270 *)
  Inductive recursive_continuation_wrapper : Type :=
    | No_wrapper
    | Wrapper_needed.

  (* PORT-GAP(type): 272-277, a record whose last field has the name of the
     type above. Rocq has one name space, and the type keeps the name (Rocq
     prints its definition): the record is a type of one constructor here,
     its fields by place, and the extracted file has the compiler's
     definition, which the directive of [t] holds. *)
  Inductive t_ : Type :=
    | Build_t (removed_aliased_params_and_extra_params : Variable_.Set_.t)
        (lets_to_introduce : Variable_.Lmap.t Simple.t)
        (extra_args_for_aliases : Variable_.Set_.t)
        (recursive_continuation_wrapper_ : recursive_continuation_wrapper).
  Extract Inductive t_ => "t"
    [ "(fun (x__1, x__2, x__3, x__4) -> { removed_aliased_params_and_extra_params = x__1; lets_to_introduce = x__2; extra_args_for_aliases = x__3; recursive_continuation_wrapper = x__4 })" ]
    "(fun f__1 x__0 -> let { removed_aliased_params_and_extra_params = x__1; lets_to_introduce = x__2; extra_args_for_aliases = x__3; recursive_continuation_wrapper = x__4 } = x__0 in f__1 x__1 x__2 x__3 x__4)".
  Definition t : Type := t_.
  Extract Constant t => "
    { removed_aliased_params_and_extra_params : Variable.Set.t;
      lets_to_introduce : Simple.t Variable.Lmap.t;
      extra_args_for_aliases : Variable.Set.t;
      recursive_continuation_wrapper : recursive_continuation_wrapper
    }".

  (* 279-297. The compiler's second parameter is the pattern of the four
     fields. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Continuation_param_aliases.t)
      : M unit :=
    let* '(Build_t removed_aliased_params_and_extra_params lets_to_introduce
             extra_args_for_aliases recursive_continuation_wrapper) :=
      ret t
    in
    (* 282-286: the compiler's function is a [function] of its second
       argument. *)
    let& pp_wrapper :=
      fun (ppf : Format.formatter) x =>
      match x with
      | No_wrapper => ret tt
      | Wrapper_needed =>
        Format.fprintf0 ppf
          "@ @[<hov 1>(recursive_continuation_wrapper needed)@]"
      end
    in
    let! tmp1 := papp1 Variable_.Lmap.print Simple.print in
    Format.fprintf8 ppf
      "@[<hov 1>(@[<hov 1>(removed_aliased_params_and_extra_params %a)@]@ @[<hov 1>(lets_to_introduce %a)@]@[<hov 1>(extra_args_for_aliases %a)@]%a)@]"
      Variable_.Set_.print removed_aliased_params_and_extra_params
      tmp1 lets_to_introduce
      Variable_.Set_.print extra_args_for_aliases
      pp_wrapper recursive_continuation_wrapper.
End Continuation_param_aliases.

(* Result of the flow analysis: alias analysis result *)
(* ************************************************** *)

(* 303-318 *)
Module Alias_result.
  (* 304-307 *)
  Record t : Type :=
    { aliases_kind : Variable_.Map.t Flambda_kind.t;
      continuation_parameters :
        Continuation.Map.t Continuation_param_aliases.t
    }.

  (* 309-317. The compiler's second parameter is the pattern
     [{ aliases_kind; continuation_parameters }]. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Alias_result.t) : M unit :=
    let* '{| Alias_result.aliases_kind := aliases_kind;
             Alias_result.continuation_parameters := continuation_parameters
          |} :=
      ret t
    in
    let! tmp1 :=
      papp1 Continuation.Map.print Continuation_param_aliases.print
    in
    let! tmp2 := papp1 Variable_.Map.print Flambda_kind.print in
    Format.fprintf4 ppf
      "@[<hov 1>(@[<hov 1>(aliases_kind@ %a)@]@ @[<hov 1>(continuation_parameters@ %a)@])@]"
      tmp2 aliases_kind
      tmp1 continuation_parameters.
End Alias_result.

(* Result of the flow analysis: mutable unboxing *)
(* ********************************************* *)

(* 323-340 *)
Module Mutable_unboxing_result.
  (* 324-328 *)
  Record t : Type :=
    { did_unbox_a_mutable_block : bool;
      additional_epa :
        Continuation.Map.t Continuation_extra_params_and_args.t;
      let_rewrites : Named_rewrite_id.Map.t Named_rewrite.t
    }.

  (* 330-339. The compiler's second parameter is the pattern
     [{ did_unbox_a_mutable_block; additional_epa; let_rewrites }]. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Mutable_unboxing_result.t)
      : M unit :=
    let* '{| Mutable_unboxing_result.did_unbox_a_mutable_block :=
               did_unbox_a_mutable_block;
             Mutable_unboxing_result.additional_epa := additional_epa;
             Mutable_unboxing_result.let_rewrites := let_rewrites
          |} :=
      ret t
    in
    let! tmp1 := papp1 Named_rewrite_id.Map.print Named_rewrite.print in
    let! tmp2 :=
      papp1 Continuation.Map.print Continuation_extra_params_and_args.print
    in
    Format.fprintf5 ppf
      "@[<hov 1>(@[<hov 1>(did_unbox_a_mutable_block@ %b)@]@ @[<hov 1>(additional_epa@ %a)@]@ @[<hov 1>(let_rewrites@ %a)@])@]"
      did_unbox_a_mutable_block
      tmp2 additional_epa
      tmp1 let_rewrites.
End Mutable_unboxing_result.

(* Result of the flow analysis *)
(* *************************** *)

(* 345-363 *)
Module Flow_result.
  (* 346-350 *)
  Record t : Type :=
    { data_flow_result : Data_flow_result.t;
      aliases_result : Alias_result.t;
      mutable_unboxing_result : Mutable_unboxing_result.t
    }.

  (* 352-362. The compiler's second parameter is the pattern
     [{ data_flow_result; aliases_result; mutable_unboxing_result; }]. *)
  (* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept. *)
  Definition print (ppf : Format.formatter) (t : Flow_result.t) : M unit :=
    let* '{| Flow_result.data_flow_result := data_flow_result;
             Flow_result.aliases_result := aliases_result;
             Flow_result.mutable_unboxing_result := mutable_unboxing_result
          |} :=
      ret t
    in
    Format.fprintf6 ppf
      "@[<hov 1>(@[<hov 1>(data_flow_result@ %a)@]@ @[<hov 1>(aliases_result@ %a)@]@ @[<hov 1>(mutable_unboxing_result@ %a)@])@]"
      Data_flow_result.print data_flow_result
      Alias_result.print aliases_result
      Mutable_unboxing_result.print mutable_unboxing_result.
End Flow_result.
