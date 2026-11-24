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

(* This file follows middle_end/flambda2/simplify/flow/mutable_unboxing.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Array Bound_parameter
  Continuation Continuation_extra_params_and_args Control_flow_graph
  Dominator_graph Flambda_debug_uid Flambda_features Flambda_kind
  Flambda_primitive Flow_types Format List Mutability Name
  Name_occurrences Named_rewrite Named_rewrite_id Numeric_types Or_null Printf
  Simple Stdlib_ Tag Target_system Value_slot Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
From SimplifyPort.abbrev.mutable_unboxing Require Import Port_abbreviations.
(*OCAML
module T = Flow_types
module EPA = Continuation_extra_params_and_args
OCAML*)

(* 16 *)

(* Types *)

(* 20-24 *)
Record block_to_unbox : Type :=
  { tag : Tag.t;
    mut : Mutability.t;
    fields_kinds : list Flambda_kind.With_subkind.t
  }.

(* 26 *)
Definition extra_params : Type := list Bound_parameter.t.

(* 28-30 *)
Definition extra_args : Type :=
  Continuation.Map.t
    (Apply_cont_rewrite_id.Map.t (Numeric_types.Int.Map.t Simple.t)).

(* PORT-GAP(loose): 32-37, the first two fields are [blocks_to_unbox] and
   [continuations_with_live_block] in the compiler; the file has functions
   of these two names (lines 211 and 305), and Rocq has one name space: the
   functions keep the names and the fields take one [_] (the type is
   abstract in the interface). *)
Record t : Type :=
  { blocks_to_unbox_ : Simple.Map.t block_to_unbox;
    continuations_with_live_block_ : Continuation.Map.t Simple.Set_.t;
    extra_params_and_args : Continuation.Map.t (extra_params * extra_args);
    rewrites : Named_rewrite_id.Map.t Named_rewrite.t
  }.

(* Escaping analysis *)

(* 41-58 *)
Definition free_names_of_apply_cont_args
    (apply_cont_args :
      Apply_cont_rewrite_id.Map.t (Numeric_types.Int.Map.t T.Cont_arg.t))
    : M Variable_.Set_.t :=
  Apply_cont_rewrite_id.Map.fold
    (fun _ args free =>
      Numeric_types.Int.Map.fold
        (fun _ arg free =>
          match arg with
          | T.Cont_arg.Function_result => ret free
          | T.Cont_arg.New_let_binding _ _ =>
            ret free (* Doesn't really matter, already escaping *)
          | T.Cont_arg.Simple s =>
            let! tmp1 := Simple.must_be_var s in
            match tmp1 with
            | None => ret free
            | Some (var, _coer) => Variable_.Set_.add var free
            end
          end)
        args free)
    apply_cont_args Variable_.Set_.empty.

(* 60-67. [Simple.pattern_match']: the arguments are in the order of the
   interface: [~var ~symbol ~const]. *)
Definition find_alias (dom : Dominator_graph.alias_map) (simple : Simple.t)
    : M Simple.t :=
  Simple.pattern_match' simple
    (fun var _ =>
      let! tmp1 := Variable_.Map.find_or_null var dom in
      match tmp1 with
      | Or_null.Null => ret simple
      | Or_null.This res => ret res
      end)
    (fun _ _ => ret simple)
    (fun _ => ret simple).

(* 69-83 *)
Definition escaping_by_alias (dom : Dominator_graph.alias_map)
    (dom_graph : Dominator_graph.t) : M Simple.Set_.t :=
  Simple.Map.fold
    (fun flow_to flow_from escaping =>
      let* alias_to := find_alias dom flow_to in
      let* new_escaping :=
        Simple.Set_.fold
          (fun flow_from escaping =>
            let* alias_from := find_alias dom flow_from in
            let* is_escaping :=
              let! tmp1 := Simple.equal alias_to alias_from in
              ret (negb tmp1)
            in
            if is_escaping
            then Simple.Set_.add alias_from escaping
            else ret escaping)
          flow_from Simple.Set_.empty
      in
      Simple.Set_.union escaping new_escaping)
    dom_graph.(Dominator_graph.graph)
    Simple.Set_.empty.

(* 85-93 *)
Definition names_escaping_from_mutable_prim (result_required : bool)
    (prim : T.Mutable_prim.t) : M Name_occurrences.t :=
  match prim with
  | T.Mutable_prim.Make_block _ _ _ fields =>
    if result_required
    then Simple.List.free_names fields
    else ret Name_occurrences.empty
  | T.Mutable_prim.Block_set _ _ _ value => Simple.free_names value
  | T.Mutable_prim.Is_int _ | T.Mutable_prim.Get_tag _
  | T.Mutable_prim.Block_load _ _ _ _ =>
    ret Name_occurrences.empty
  end.

(* 95-109 *)
Definition names_used_in_new_let_binding (elt : T.Continuation_info.t)
    : M Variable_.Set_.t :=
  Continuation.Map.fold
    (fun _cont apply_cont_args vars =>
      Apply_cont_rewrite_id.Map.fold
        (fun _ args vars =>
          Numeric_types.Int.Map.fold
            (fun _ arg vars =>
              match arg with
              | T.Cont_arg.Function_result | T.Cont_arg.Simple _ => ret vars
              | T.Cont_arg.New_let_binding _ deps =>
                Name_occurrences.fold_variables deps vars (fun vars v =>
                  Variable_.Set_.add v vars)
              end)
            args vars)
        apply_cont_args vars)
    elt.(Flow_types.Continuation_info.apply_cont_args)
    Variable_.Set_.empty.

(* 111-164 *)
Definition escaping_by_use_for_one_continuation (required_names : Name.Set_.t)
    (dom : Dominator_graph.alias_map) (elt : T.Continuation_info.t)
    : M Simple.Set_.t :=
  let& add_name_occurrences :=
    fun (occurrences : Name_occurrences.t) (init : Simple.Set_.t) =>
    Name_occurrences.fold_variables occurrences init (fun escaping var =>
      let* escaping :=
        let! tmp1 := Variable_.Map.find_or_null var dom in
        match tmp1 with
        | Or_null.Null => ret escaping
        | Or_null.This simple => Simple.Set_.add simple escaping
        end
      in
      let! tmp1 := Simple.var var in
      Simple.Set_.add tmp1 escaping)
  in
  let* escaping :=
    add_name_occurrences elt.(Flow_types.Continuation_info.used_in_handler)
      Simple.Set_.empty
  in
  let* escaping :=
    Name.Map.fold
      (fun name deps escaping =>
        let! tmp1 := Name.Set_.mem name required_names in
        if tmp1 then add_name_occurrences deps escaping else ret escaping)
      elt.(Flow_types.Continuation_info.bindings)
      escaping
  in
  let* escaping :=
    (* CR ncourant: we could track primitives here as other primitives here
       (mainly [Block_load]), but the usefulness of this is unclear for now.

       See [flambda2/tests/ref_to_var/unboxing_cse.ml] *)
    let! tmp1 := names_used_in_new_let_binding elt in
    Variable_.Set_.fold
      (fun var escaping =>
        let! tmp2 := Variable_.Map.find_or_null var dom in
        match tmp2 with
        | Or_null.Null => ret escaping
        | Or_null.This simple => Simple.Set_.add simple escaping
        end)
      tmp1 escaping
  in
  let* escaping :=
    Value_slot.Map.fold
      (fun _value_slot map escaping =>
        Name.Map.fold
          (fun _closure_name values_in_env escaping =>
            add_name_occurrences values_in_env escaping)
          map escaping)
      elt.(Flow_types.Continuation_info.value_slots)
      escaping
  in
  (* 153-163: the second argument of the function is the pattern
     [T.Mutable_let_prim.{ prim; bound_var; _ }]. *)
  let* escaping :=
    List.fold_left
      (fun escaping pat =>
        let* '{| T.Mutable_let_prim.prim := prim;
                 T.Mutable_let_prim.bound_var := bound_var
              |} :=
          ret pat
        in
        let* result_required :=
          let! tmp1 := Name.var bound_var in
          Name.Set_.mem tmp1 required_names
        in
        let! tmp1 := names_escaping_from_mutable_prim result_required prim in
        add_name_occurrences tmp1 escaping)
      escaping
      elt.(Flow_types.Continuation_info.mutable_let_prims_rev)
  in
  ret escaping.

(* 166-173 *)
Definition escaping_by_use (required_names : Name.Set_.t)
    (dom : Dominator_graph.alias_map) (source_info : T.Acc.t)
    : M Simple.Set_.t :=
  Continuation.Map.fold
    (fun _cont elt escaping =>
      let! tmp1 :=
        escaping_by_use_for_one_continuation required_names dom elt
      in
      Simple.Set_.union tmp1 escaping)
    source_info.(Flow_types.Acc.map)
    Simple.Set_.empty.

(* 175-196 *)
Definition escaping_by_return (dom : Dominator_graph.alias_map)
    (source_info : T.Acc.t)
    (return_continuation exn_continuation : Continuation.t)
    : M Simple.Set_.t :=
  Continuation.Map.fold
    (fun _cont (elt : T.Continuation_info.t) escaping =>
      let& add_escaping :=
        fun (cont : Continuation.t) (escaping : Simple.Set_.t) =>
        let! tmp1 :=
          Continuation.Map.find_or_null cont
            elt.(Flow_types.Continuation_info.apply_cont_args)
        in
        match tmp1 with
        | Or_null.Null => ret escaping
        | Or_null.This apply_cont_args =>
          let! tmp2 := free_names_of_apply_cont_args apply_cont_args in
          Variable_.Set_.fold
            (fun var escaping =>
              let* escaping :=
                let! tmp3 := Variable_.Map.find_or_null var dom in
                match tmp3 with
                | Or_null.Null => ret escaping
                | Or_null.This simple => Simple.Set_.add simple escaping
                end
              in
              let! tmp3 := Simple.var var in
              Simple.Set_.add tmp3 escaping)
            tmp2 escaping
        end
      in
      let* escaping := add_escaping return_continuation escaping in
      add_escaping exn_continuation escaping)
    source_info.(Flow_types.Acc.map)
    Simple.Set_.empty.

(* 198-207 *)
Definition escaping (dom : Dominator_graph.alias_map)
    (dom_graph : Dominator_graph.t) (source_info : T.Acc.t)
    (return_continuation exn_continuation : Continuation.t)
    (required_names : Name.Set_.t) : M Simple.Set_.t :=
  let* escaping_by_alias := escaping_by_alias dom dom_graph in
  let* escaping_by_use := escaping_by_use required_names dom source_info in
  let* escaping_by_return :=
    escaping_by_return dom source_info return_continuation exn_continuation
  in
  let! tmp1 := Simple.Set_.union escaping_by_return escaping_by_use in
  Simple.Set_.union escaping_by_alias tmp1.

(* *)

(* 211-252 *)
Definition blocks_to_unbox (escaping : Simple.Set_.t) (source_info : T.Acc.t)
    (required_names : Name.Set_.t) : M (Simple.Map.t block_to_unbox) :=
  Continuation.Map.fold
    (fun _cont (elt : T.Continuation_info.t) map =>
      (* 215: the second argument of the function is the pattern
         [T.Mutable_let_prim.{ bound_var = var; prim; _ }]. *)
      List.fold_left
        (fun map pat =>
          let* '{| T.Mutable_let_prim.bound_var := var;
                   T.Mutable_let_prim.prim := prim
                |} :=
            ret pat
          in
          match prim with
          | T.Mutable_prim.Block_load _ _ _ _ | T.Mutable_prim.Block_set _ _ _ _
          | T.Mutable_prim.Is_int _ | T.Mutable_prim.Get_tag _ =>
            ret map
          | T.Mutable_prim.Make_block kind mut _ fields =>
            (* We do not want to try to unbox blocks that are not required. It
               is not only an optimization issue, but also a correctness one:
               since a block that is not required does not mark its fields as
               escaping, unboxing non-required blocks might keep alive a
               reference to another unboxed block, while the primitive for
               creating it was removed. *)
            let! tmp1 := Simple.var var in
            let! tmp2 := Simple.Set_.mem tmp1 escaping in
            let! tmp3 :=
              or_else tmp2
                (let! tmp4 := Name.var var in
                 let! tmp5 := Name.Set_.mem tmp4 required_names in
                 ret (negb tmp5))
            in
            if tmp3
            then ret map
            else
              let* block_to_unbox :=
                match kind with
                | Flambda_primitive.Block_kind.Values tag fields_kinds =>
                  let! tmp1 := Tag.Scannable.to_tag tag in
                  ret
                    {| Mutable_unboxing.tag := tmp1;
                       Mutable_unboxing.mut := mut;
                       Mutable_unboxing.fields_kinds := fields_kinds
                    |}
                | Flambda_primitive.Block_kind.Naked_floats =>
                  let! tmp1 :=
                    List.map
                      (fun _ => ret Flambda_kind.With_subkind.naked_float)
                      fields
                  in
                  ret
                    {| Mutable_unboxing.tag := Tag.double_array_tag;
                       Mutable_unboxing.mut := mut;
                       Mutable_unboxing.fields_kinds := tmp1
                    |}
                | Flambda_primitive.Block_kind.Mixed tag shape =>
                  let* fields_kinds :=
                    let! tmp1 :=
                      Flambda_kind.Mixed_block_shape.field_kinds shape
                    in
                    let! tmp2 := Array.to_list tmp1 in
                    List.map Flambda_kind.With_subkind.anything tmp2
                  in
                  let! tmp1 := Tag.Scannable.to_tag tag in
                  ret
                    {| Mutable_unboxing.tag := tmp1;
                       Mutable_unboxing.mut := mut;
                       Mutable_unboxing.fields_kinds := fields_kinds
                    |}
                end
              in
              let! tmp1 := Simple.var var in
              Simple.Map.add tmp1 block_to_unbox map
          end)
        map
        elt.(Flow_types.Continuation_info.mutable_let_prims_rev))
    source_info.(Flow_types.Acc.map)
    Simple.Map.empty.

(* 254-268 *)
Definition prims_using_block (blocks_to_unbox : Simple.Map.t block_to_unbox)
    (dom : Dominator_graph.alias_map) (prim : T.Mutable_prim.t)
    : M Simple.Set_.t :=
  match prim with
  | T.Mutable_prim.Make_block _ _ _ _ => ret Simple.Set_.empty
  | T.Mutable_prim.Is_int block
  | T.Mutable_prim.Get_tag block
  | T.Mutable_prim.Block_set _ block _ _
  | T.Mutable_prim.Block_load _ _ block _ =>
    let* block :=
      let! tmp1 := Variable_.Map.find_or_null block dom in
      match tmp1 with
      | Or_null.Null => Simple.var block
      | Or_null.This block => ret block
      end
    in
    let! tmp1 := Simple.Map.mem block blocks_to_unbox in
    if tmp1 then Simple.Set_.singleton block else ret Simple.Set_.empty
  end.

(* 270-285 *)
Definition continuations_using_blocks
    (blocks_to_unbox : Simple.Map.t block_to_unbox)
    (dom : Dominator_graph.alias_map) (source_info : T.Acc.t)
    : M (Continuation.Map.t Simple.Set_.t) :=
  Continuation.Map.mapi
    (fun _cont (elt : T.Continuation_info.t) =>
      (* 275: the second argument of the function is the pattern
         [T.Mutable_let_prim.{ prim; _ }]. *)
      let* used :=
        List.fold_left
          (fun used_block pat =>
            let* '{| T.Mutable_let_prim.prim := prim |} := ret pat in
            let! tmp1 := prims_using_block blocks_to_unbox dom prim in
            Simple.Set_.union used_block tmp1)
          Simple.Set_.empty
          elt.(Flow_types.Continuation_info.mutable_let_prims_rev)
      in
      (let! tmp1 := Simple.Set_.is_empty used in
       let! tmp2 := and_then (negb tmp1) (Flambda_features.dump_flow tt) in
       if tmp2
       then
         Format.printf4 "Cont using block %a %a@." Continuation.print _cont
           Simple.Set_.print used
       else ret tt) ;;
      ret used)
    source_info.(Flow_types.Acc.map).

(* 287-303 *)
Definition continuations_defining_blocks
    (blocks_to_unbox : Simple.Map.t block_to_unbox) (source_info : T.Acc.t)
    : M (Continuation.Map.t Simple.Set_.t) :=
  Continuation.Map.mapi
    (fun _cont (elt : T.Continuation_info.t) =>
      (* 292: the second argument of the function is the pattern
         [T.Mutable_let_prim.{ bound_var = var; _ }]. *)
      let* defined :=
        List.fold_left
          (fun defined_blocks pat =>
            let* '{| T.Mutable_let_prim.bound_var := var |} := ret pat in
            let! tmp1 := Simple.var var in
            let! tmp2 := Simple.Map.mem tmp1 blocks_to_unbox in
            if tmp2
            then
              let! tmp3 := Simple.var var in
              Simple.Set_.add tmp3 defined_blocks
            else ret defined_blocks)
          Simple.Set_.empty
          elt.(Flow_types.Continuation_info.mutable_let_prims_rev)
      in
      (let! tmp1 := Simple.Set_.is_empty defined in
       let! tmp2 := and_then (negb tmp1) (Flambda_features.dump_flow tt) in
       if tmp2
       then
         Format.printf4 "Cont defining block %a %a@." Continuation.print _cont
           Simple.Set_.print defined
       else ret tt) ;;
      ret defined)
    source_info.(Flow_types.Acc.map).

(* 305-340. In the compiler: [~blocks_to_unbox ~dom ~source_info
   ~control_flow_graph]. *)
Definition continuations_with_live_block
    (blocks_to_unbox : Simple.Map.t block_to_unbox)
    (dom : Dominator_graph.alias_map) (source_info : T.Acc.t)
    (control_flow_graph : Control_flow_graph.t)
    : M (Continuation.Map.t Simple.Set_.t) :=
  let* continuations_defining_blocks :=
    continuations_defining_blocks blocks_to_unbox source_info
  in
  let* continuations_using_blocks :=
    continuations_using_blocks blocks_to_unbox dom source_info
  in
  let* continuations_using_blocks_but_not_defining_them :=
    Continuation.Map.merge
      (fun _cont defined used =>
        match defined, used with
        | None, None => assert_false (* *)
        | None, Some _used =>
          fatal_errorf0
            "In Data_flow: incomplete map of continuation defining blocks"
        | Some _defined, None =>
          fatal_errorf0
            "In Data_flow: incomplete map of continuation using blocks"
        | Some defined, Some used =>
          let! tmp1 := Simple.Set_.diff used defined in
          ret (Some tmp1)
        end)
      continuations_defining_blocks continuations_using_blocks
  in
  Control_flow_graph.fixpoint control_flow_graph
    continuations_using_blocks_but_not_defining_them Simple.Set_.equal
    (fun caller old_using_blocks _ used_blocks =>
      let* defined_blocks :=
        Continuation.Map.find caller continuations_defining_blocks
      in
      let! tmp1 := Simple.Set_.union old_using_blocks used_blocks in
      Simple.Set_.diff tmp1 defined_blocks).

(* 342-351: the first argument of the function is the pair
   [(i, fields)]. *)
Definition list_to_int_map {A : Type} (l : list A)
    : M (Numeric_types.Int.Map.t A) :=
  let* '(_, map) :=
    List.fold_left
      (fun pat elt =>
        let* '(i, fields) := ret pat in
        let* fields := Numeric_types.Int.Map.add i elt fields in
        ret (i + 1, fields))
      (0, Numeric_types.Int.Map.empty)
      l
  in
  ret map.

(* 353 *)
Definition int_map_to_list {A : Type} (m : Numeric_types.Int.Map.t A)
    : M (list A) :=
  let! tmp1 := Numeric_types.Int.Map.bindings m in
  List.map Stdlib_.snd tmp1.

(* 355-573 *)
Module Fold_prims.
  (* 356-360 *)
  Record env : Type :=
    { bindings : Simple.Map.t (Numeric_types.Int.Map.t Simple.t);
      (* non escaping / unboxed blocks fields values *)
      rewrites : Named_rewrite_id.Map.t Named_rewrite.t
    }.

  (* 362-370. In the compiler: [~block ~dom ~env ~blocks_to_unbox ~f], and
     [f ~block ~tag ~fields_kinds]. *)
  Definition with_unboxed_block (block : Variable_.t)
      (dom : Dominator_graph.alias_map) (env : Fold_prims.env)
      (blocks_to_unbox : Simple.Map.t block_to_unbox)
      (f :
        Simple.t -> Tag.t -> list Flambda_kind.With_subkind.t
        -> M Fold_prims.env) : M Fold_prims.env :=
    let* block :=
      let! tmp1 := Variable_.Map.find_or_null block dom in
      match tmp1 with
      | Or_null.Null => Simple.var block
      | Or_null.This block => ret block
      end
    in
    let! tmp1 := Simple.Map.find_or_null block blocks_to_unbox in
    match tmp1 with
    | Or_null.Null => ret env
    | Or_null.This
        {| Mutable_unboxing.tag := tag;
           Mutable_unboxing.fields_kinds := fields_kinds;
           Mutable_unboxing.mut := _
        |} =>
      f block tag fields_kinds
    end.

  (* 372-380. In the compiler: [~block ~dom ~env ~f], and [f ~block
     fields]. *)
  Definition with_unboxed_fields (block : Variable_.t)
      (dom : Dominator_graph.alias_map) (env : Fold_prims.env)
      (f :
        Simple.t -> Numeric_types.Int.Map.t Simple.t -> M Fold_prims.env)
      : M Fold_prims.env :=
    let* block :=
      let! tmp1 := Variable_.Map.find_or_null block dom in
      match tmp1 with
      | Or_null.Null => Simple.var block
      | Or_null.This block => ret block
      end
    in
    let! tmp1 := Simple.Map.find_or_null block env.(Fold_prims.bindings) in
    match tmp1 with
    | Or_null.Null => ret env
    | Or_null.This fields => f block fields
    end.

  (* 382-465 *)
  Definition apply_prim (machine_width : Target_system.Machine_width.t)
      (dom : Dominator_graph.alias_map)
      (blocks_to_unbox : Simple.Map.t block_to_unbox) (env : Fold_prims.env)
      (rewrite_id : Named_rewrite_id.t) (var : Variable_.t)
      (prim : T.Mutable_prim.t) : M Fold_prims.env :=
    match prim with
    | T.Mutable_prim.Is_int block =>
      with_unboxed_fields block dom env (fun block _fields =>
        ignore block ;;
        (* ensure that only the canonical alias of block is in scope *)
        (* We only consider for unboxing vluaes which are aliases to a single
           makeblock. In particular, for variants, this means that we only
           consider for unboxing variant values which are blocks. *)
        let* bound_to := Simple.untagged_const_bool machine_width false in
        let* rewrite :=
          let! tmp1 :=
            Named_rewrite.Prim_rewrite.replace_by_binding var bound_to
          in
          Named_rewrite.prim_rewrite tmp1
        in
        let! tmp1 :=
          Named_rewrite_id.Map.add rewrite_id rewrite
            env.(Fold_prims.rewrites)
        in
        ret
          {| Fold_prims.bindings := env.(Fold_prims.bindings);
             Fold_prims.rewrites := tmp1
          |})
    | T.Mutable_prim.Get_tag block =>
      with_unboxed_block block dom env blocks_to_unbox
        (fun block tag _ =>
          ignore block ;;
          (* ensure that only the canonical alias of block is in scope *)
          let* bound_to :=
            let! tmp1 := Tag.to_targetint_31_63 machine_width tag in
            Simple.untagged_const_int tmp1
          in
          let* rewrite :=
            let! tmp1 :=
              Named_rewrite.Prim_rewrite.replace_by_binding var bound_to
            in
            Named_rewrite.prim_rewrite tmp1
          in
          let! tmp1 :=
            Named_rewrite_id.Map.add rewrite_id rewrite
              env.(Fold_prims.rewrites)
          in
          ret
            {| Fold_prims.bindings := env.(Fold_prims.bindings);
               Fold_prims.rewrites := tmp1
            |})
    | T.Mutable_prim.Block_load bak _ block field =>
      with_unboxed_fields block dom env (fun block fields =>
        ignore block ;;
        (* ensure that only the canonical alias of block is in scope *)
        let* k :=
          Flambda_primitive.Block_access_kind.element_kind_for_load bak
        in
        (* 422-428: [match .. with bound_to when c -> e1 | _ | (exception
           Not_found) -> e2]: the guard is an [if] in the case of a value,
           and [e2] is written twice. *)
        let* rewrite :=
          match_exn
            (fun _ => Numeric_types.Int.Map.find field fields)
            Not_found
            (fun _ =>
              let! tmp1 := Named_rewrite.Prim_rewrite.invalid k in
              Named_rewrite.prim_rewrite tmp1)
            (fun bound_to =>
              let! tmp1 := Simple.kind bound_to in
              let! tmp2 := Flambda_kind.equal tmp1 k in
              if tmp2
              then
                let! tmp3 :=
                  Named_rewrite.Prim_rewrite.replace_by_binding var bound_to
                in
                Named_rewrite.prim_rewrite tmp3
              else
                let! tmp3 := Named_rewrite.Prim_rewrite.invalid k in
                Named_rewrite.prim_rewrite tmp3)
        in
        let! tmp1 :=
          Named_rewrite_id.Map.add rewrite_id rewrite
            env.(Fold_prims.rewrites)
        in
        ret
          {| Fold_prims.bindings := env.(Fold_prims.bindings);
             Fold_prims.rewrites := tmp1
          |})
    | T.Mutable_prim.Block_set _ block field value =>
      with_unboxed_fields block dom env (fun block fields =>
        (let! tmp1 := Flambda_features.dump_flow tt in
         if tmp1
         then Format.printf2 "Remove Block set %a@." Variable_.print var
         else ret tt) ;;
        (* 437-449: [match .. with previous_value when c -> e1 | _ |
           (exception Not_found) -> e2]: the guard is an [if] in the case of
           a value, and [e2] is written twice. *)
        let* '(rewrite, fields) :=
          match_exn
            (fun _ => Numeric_types.Int.Map.find field fields)
            Not_found
            (fun _ =>
              let! tmp1 :=
                Named_rewrite.Prim_rewrite.invalid Flambda_kind.value
              in
              let! tmp2 := Named_rewrite.prim_rewrite tmp1 in
              ret (tmp2, fields))
            (fun previous_value =>
              let! tmp1 := Simple.kind value in
              let! tmp2 := Simple.kind previous_value in
              let! tmp3 := Flambda_kind.equal tmp2 tmp1 in
              if tmp3
              then
                let! tmp4 := Numeric_types.Int.Map.add field value fields in
                let! tmp5 :=
                  Named_rewrite.prim_rewrite
                    Named_rewrite.Prim_rewrite.remove_prim
                in
                ret (tmp5, tmp4)
              else
                let! tmp4 :=
                  Named_rewrite.Prim_rewrite.invalid Flambda_kind.value
                in
                let! tmp5 := Named_rewrite.prim_rewrite tmp4 in
                ret (tmp5, fields))
        in
        (* PORT-GAP(record-order): 450-452, a record with a call in each of
           its two fields: the last field of the type first. *)
        let* rewrites :=
          Named_rewrite_id.Map.add rewrite_id rewrite
            env.(Fold_prims.rewrites)
        in
        let* bindings :=
          Simple.Map.add block fields env.(Fold_prims.bindings)
        in
        ret
          {| Fold_prims.bindings := bindings;
             Fold_prims.rewrites := rewrites
          |})
    | T.Mutable_prim.Make_block _ _ _ fields =>
      let! tmp1 := Simple.var var in
      let! tmp2 := Simple.Map.mem tmp1 blocks_to_unbox in
      if negb tmp2
      then ret env
      else (
        (let! tmp3 := Flambda_features.dump_flow tt in
         if tmp3
         then Format.printf2 "Remove Makeblock %a@." Variable_.print var
         else ret tt) ;;
        let* rewrite :=
          Named_rewrite.prim_rewrite Named_rewrite.Prim_rewrite.remove_prim
        in
        let* fields := list_to_int_map fields in
        (* PORT-GAP(record-order): 463-465, a record with a call in each of
           its two fields: the last field of the type first. *)
        let* rewrites :=
          Named_rewrite_id.Map.add rewrite_id rewrite
            env.(Fold_prims.rewrites)
        in
        let* bindings :=
          let! tmp3 := Simple.var var in
          Simple.Map.add tmp3 fields env.(Fold_prims.bindings)
        in
        ret
          {| Fold_prims.bindings := bindings;
             Fold_prims.rewrites := rewrites
          |})
    end.

  (* 467-513 *)
  Definition init_env (blocks_to_unbox : Simple.Map.t block_to_unbox)
      (blocks_needed : Simple.Set_.t)
      (rewrites : Named_rewrite_id.Map.t Named_rewrite.t)
      : M (Fold_prims.env * list Bound_parameter.t) :=
    (* 471: the second argument of the function is the pair
       [(env, params)]. *)
    let* '(env, params) :=
      Simple.Set_.fold
        (fun block_needed pat =>
          let* '(env, params) := ret pat in
          let* '{| Mutable_unboxing.tag := _;
                   Mutable_unboxing.mut := _;
                   Mutable_unboxing.fields_kinds := fields_kinds
                |} :=
            Simple.Map.find block_needed blocks_to_unbox
          in
          let* block_params :=
            List.mapi
              (fun i kind =>
                let* name :=
                  Simple.pattern_match' block_needed
                    (fun var _ => Variable_.canonical_name var)
                    (fun _ _ =>
                      fatal_errorf0
                        "[Mutable Unboxing] Cannot unbox mutable symbols")
                    (fun _ =>
                      fatal_errorf0
                        "[Mutable Unboxing] Cannot unbox constants")
                in
                let* var :=
                  let! tmp1 := Flambda_kind.With_subkind.kind kind in
                  let! tmp2 := Printf.sprintf2 "%s_%i" name i in
                  Variable_.create None tmp2 tmp1
                in
                let& var_duid := Flambda_debug_uid.none in
                (* CR sspies: Improve the debug UID here in the future. *)
                Bound_parameter.create var kind var_duid)
              fields_kinds
          in
          let* env :=
            let* fields :=
              let! tmp1 :=
                List.map
                  (fun bp =>
                    let! tmp2 := Bound_parameter.var bp in
                    Simple.var tmp2)
                  block_params
              in
              list_to_int_map tmp1
            in
            let! tmp1 :=
              Simple.Map.add block_needed fields env.(Fold_prims.bindings)
            in
            ret
              {| Fold_prims.bindings := tmp1;
                 Fold_prims.rewrites := env.(Fold_prims.rewrites)
              |}
          in
          let! tmp1 := List.rev_append block_params params in
          ret (env, tmp1))
        blocks_needed
        ({| Fold_prims.bindings := Simple.Map.empty;
            Fold_prims.rewrites := rewrites
         |},
         [])
    in
    let! tmp1 := List.rev params in
    ret (env, tmp1).

  (* 515-523 *)
  Definition append_int_map {A : Type} (i1 i2 : Numeric_types.Int.Map.t A)
      : M (Numeric_types.Int.Map.t A) :=
    let! tmp1 := Numeric_types.Int.Map.is_empty i1 in
    if tmp1
    then ret i2
    else
      let* '(max, _) := Numeric_types.Int.Map.max_binding i1 in
      let* shifted_i2 :=
        Numeric_types.Int.Map.map_keys (fun i => ret (i + max + 1)) i2
      in
      Numeric_types.Int.Map.disjoint_union None None i1 shifted_i2.

  (* 525-572 *)
  Definition compute_rewrites (machine_width : Target_system.Machine_width.t)
      (blocks_to_unbox : Simple.Map.t block_to_unbox)
      (continuations_with_live_block : Continuation.Map.t Simple.Set_.t)
      (dom : Dominator_graph.alias_map) (source_info : T.Acc.t)
      : M
          (Continuation.Map.t (extra_params * extra_args)
           * Named_rewrite_id.Map.t Named_rewrite.t) :=
    let* rewrites := mk_ref Named_rewrite_id.Map.empty in
    let* extra_params_and_args :=
      Continuation.Map.mapi
        (fun cont (blocks_needed : Simple.Set_.t) =>
          let* elt := Continuation.Map.find cont source_info.(Flow_types.Acc.map) in
          let* '(env, extra_block_params) :=
            let! tmp1 := get rewrites in
            init_env blocks_to_unbox blocks_needed tmp1
          in
          (* 538-540: the second argument of the function is the pattern
             [T.Mutable_let_prim.{ named_rewrite_id; bound_var; prim;
             original_prim = _ }]. *)
          let* env :=
            let! tmp1 :=
              List.rev
                elt.(Flow_types.Continuation_info.mutable_let_prims_rev)
            in
            List.fold_left
              (fun env pat =>
                let* '{| T.Mutable_let_prim.named_rewrite_id :=
                           named_rewrite_id;
                         T.Mutable_let_prim.bound_var := bound_var;
                         T.Mutable_let_prim.prim := prim;
                         T.Mutable_let_prim.original_prim := _
                      |} :=
                  ret pat
                in
                apply_prim machine_width dom blocks_to_unbox env
                  named_rewrite_id bound_var prim)
              env tmp1
          in
          set rewrites env.(Fold_prims.rewrites) ;;
          let& blocks_params_to_add :=
            fun (cont : Continuation.t)
                (rewrites :
                  Apply_cont_rewrite_id.Map.t
                    (Numeric_types.Int.Map.t T.Cont_arg.t)) =>
            Apply_cont_rewrite_id.Map.map
              (fun _args =>
                let! tmp1 :=
                  Continuation.Map.find_or_null cont
                    continuations_with_live_block
                in
                match tmp1 with
                | Or_null.Null => ret Numeric_types.Int.Map.empty
                | Or_null.This blocks_needed =>
                  let* extra_args :=
                    Simple.Set_.fold
                      (fun block_needed extra_args =>
                        let* args :=
                          Simple.Map.find block_needed
                            env.(Fold_prims.bindings)
                        in
                        append_int_map extra_args args)
                      blocks_needed Numeric_types.Int.Map.empty
                  in
                  ret extra_args
                end)
              rewrites
          in
          let* new_apply_cont_args :=
            Continuation.Map.mapi blocks_params_to_add
              elt.(Flow_types.Continuation_info.apply_cont_args)
          in
          ret (extra_block_params, new_apply_cont_args))
        continuations_with_live_block
    in
    let! tmp1 := get rewrites in
    ret (extra_params_and_args, tmp1).
End Fold_prims.

(* 575-616. In the compiler: [~dom ~dom_graph ~source_info
   ~control_flow_graph ~required_names ~return_continuation
   ~exn_continuation ~machine_width]. *)
Definition create (dom : Dominator_graph.alias_map)
    (dom_graph : Dominator_graph.t) (source_info : T.Acc.t)
    (control_flow_graph : Control_flow_graph.t) (required_names : Name.Set_.t)
    (return_continuation exn_continuation : Continuation.t)
    (machine_width : Target_system.Machine_width.t) : M Mutable_unboxing.t :=
  let* escaping :=
    escaping dom dom_graph source_info return_continuation exn_continuation
      required_names
  in
  let* blocks_to_unbox := blocks_to_unbox escaping source_info required_names in
  (* 585-594 *)
  (let! tmp1 := Simple.Map.is_empty blocks_to_unbox in
   let! tmp2 := and_then (negb tmp1) (Flambda_features.dump_flow tt) in
   if tmp2
   then
     (* PORT-GAP(papp): 589-593, [Simple.Map.print] is given its first
        argument only, and [Format.pp_print_list] its first two; the
        argument of the function is the pattern [{ tag; fields_kinds; mut
        }]. *)
     let! tmp3 :=
       papp1 Simple.Map.print (fun ppf pat =>
         let* '{| Mutable_unboxing.tag := tag;
                  Mutable_unboxing.fields_kinds := fields_kinds;
                  Mutable_unboxing.mut := mut
               |} :=
           ret pat
         in
         let! tmp4 :=
           papp2 Format.pp_print_list (Some Format.pp_print_space)
             Flambda_kind.With_subkind.print
         in
         Format.fprintf6 ppf "{%a}(%a)[%a]" Tag.print tag Mutability.print mut
           tmp4 fields_kinds)
     in
     Format.printf2 "Non escaping makeblocks %a@." tmp3 blocks_to_unbox
   else ret tt) ;;
  let* continuations_with_live_block :=
    continuations_with_live_block blocks_to_unbox dom source_info
      control_flow_graph
  in
  let* toplevel_used :=
    Continuation.Map.find source_info.(Flow_types.Acc.dummy_toplevel_cont)
      continuations_with_live_block
  in
  (let! tmp1 := Simple.Set_.is_empty toplevel_used in
   if negb tmp1
   then
     fatal_errorf2
       "Toplevel continuation cannot have needed extra argument for block: %a@."
       Simple.Set_.print toplevel_used
   else ret tt) ;;
  let* '(extra_params_and_args, rewrites) :=
    Fold_prims.compute_rewrites machine_width blocks_to_unbox
      continuations_with_live_block dom source_info
  in
  ret
    {| Mutable_unboxing.extra_params_and_args := extra_params_and_args;
       Mutable_unboxing.blocks_to_unbox_ := blocks_to_unbox;
       Mutable_unboxing.continuations_with_live_block_ :=
         continuations_with_live_block;
       Mutable_unboxing.rewrites := rewrites
    |}.

(* 618-621. The compiler's first parameter is the pattern
   [{ blocks_to_unbox = _; continuations_with_live_block; _ }]. *)
Definition pp_node (t : Mutable_unboxing.t) (ppf : Format.formatter)
    (cont : Continuation.t) : M unit :=
  let* '{| Mutable_unboxing.blocks_to_unbox_ := _;
           Mutable_unboxing.continuations_with_live_block_ :=
             continuations_with_live_block
        |} :=
    ret t
  in
  let! tmp1 := Continuation.Map.find_or_null cont continuations_with_live_block in
  match tmp1 with
  | Or_null.Null => ret tt
  | Or_null.This live_blocks =>
    Format.fprintf2 ppf " %a" Simple.Set_.print live_blocks
  end.

(* 623-700 *)
Definition add_to_extra_params_and_args (result : Mutable_unboxing.t)
    : M (Continuation.Map.t EPA.t) :=
  let& epa := Continuation.Map.empty in
  (* 628: the second argument of the function is the pair [(_extra_params,
     extra_args)]. *)
  let* extra_block_args :=
    Continuation.Map.fold
      (fun _caller_cont pat all_extra_args =>
        let* '(_extra_params, extra_args) := ret pat in
        Continuation.Map.fold
          (fun callee_cont
               (caller_extra_args :
                 Apply_cont_rewrite_id.Map.t (Numeric_types.Int.Map.t Simple.t))
               (all_extra_args :
                 Continuation.Map.t
                   (list (Apply_cont_rewrite_id.Map.t EPA.Extra_arg.t))) =>
            Continuation.Map.update callee_cont
              (fun previous_extra_args =>
                let* previous_extra_args :=
                  match previous_extra_args with
                  | None =>
                    let! tmp1 :=
                      Continuation.Map.find_or_null callee_cont
                        result.(Mutable_unboxing.extra_params_and_args)
                    in
                    match tmp1 with
                    | Or_null.Null => ret []
                    | Or_null.This (extra_params, _) =>
                      List.map
                        (fun _ => ret Apply_cont_rewrite_id.Map.empty)
                        extra_params
                    end
                  | Some extra_args => ret extra_args
                  end
                in
                let* extra_args :=
                  Apply_cont_rewrite_id.Map.fold
                    (fun rewrite_id (args : Numeric_types.Int.Map.t Simple.t)
                         (previous_extra_args :
                           list (Apply_cont_rewrite_id.Map.t EPA.Extra_arg.t)) =>
                      let* args := int_map_to_list args in
                      List.map2
                        (fun arg previous_extra_args =>
                          Apply_cont_rewrite_id.Map.add rewrite_id
                            (EPA.Extra_arg.Already_in_scope arg)
                            previous_extra_args)
                        args previous_extra_args)
                    caller_extra_args previous_extra_args
                in
                ret (Some extra_args))
              all_extra_args)
          extra_args all_extra_args)
      result.(Mutable_unboxing.extra_params_and_args)
      Continuation.Map.empty
  in
  let* epa :=
    Continuation.Map.fold
      (fun cont extra_args epa =>
        let* extra_params :=
          let! tmp1 :=
            Continuation.Map.find_or_null cont
              result.(Mutable_unboxing.extra_params_and_args)
          in
          match tmp1 with
          | Or_null.Null => ret []
          | Or_null.This (extra_params, _) => ret extra_params
          end
        in
        Continuation.Map.update cont
          (fun epa_for_cont =>
            let& epa_for_cont :=
              match epa_for_cont with None => EPA.empty | Some epa => epa end
            in
            (* 690-694: [EPA.add epa_for_cont ~extra_param ~extra_args
               ~invalids]: the arguments are in the order of the
               interface. *)
            let* epa_for_cont :=
              List.fold_left2
                (fun epa_for_cont extra_param extra_args =>
                  EPA.add epa_for_cont Apply_cont_rewrite_id.Set_.empty
                    extra_param extra_args)
                epa_for_cont extra_params extra_args
            in
            ret (Some epa_for_cont))
          epa)
      extra_block_args epa
  in
  ret epa.

(* 702-708 *)
Definition did_unbox_a_mutable_block (result : Mutable_unboxing.t) : M bool :=
  Simple.Map.exists_
    (fun _simple block_to_unbox =>
      match block_to_unbox.(Mutable_unboxing.mut) with
      | Mutability.Mutable => ret true
      | Mutability.Immutable_unique | Mutability.Immutable => ret false
      end)
    result.(Mutable_unboxing.blocks_to_unbox_).

(* 710-716 *)
Definition make_result (result : Mutable_unboxing.t)
    : M (T.Mutable_unboxing_result.t * Simple.Set_.t) :=
  let* additional_epa := add_to_extra_params_and_args result in
  let& let_rewrites := result.(Mutable_unboxing.rewrites) in
  let* did_unbox_a_mutable_block := did_unbox_a_mutable_block result in
  let! tmp1 := Simple.Map.keys result.(Mutable_unboxing.blocks_to_unbox_) in
  ret
    ({| T.Mutable_unboxing_result.did_unbox_a_mutable_block :=
          did_unbox_a_mutable_block;
        T.Mutable_unboxing_result.additional_epa := additional_epa;
        T.Mutable_unboxing_result.let_rewrites := let_rewrites
     |},
     tmp1).
