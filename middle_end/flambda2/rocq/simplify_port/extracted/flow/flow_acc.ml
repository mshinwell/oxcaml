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

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/flow/Flow_acc.v, which follows
   middle_end/flambda2/simplify/flow/flow_acc.ml function by function. Do not
   edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module T = Flow_types
module EPA = Continuation_extra_params_and_args
open Port_abbreviations
open Port_monad

type t = T.Acc.t

type cont_info = T.Continuation_info.t

(** val print : Format.formatter -> t -> unit coq_M **)

let print = T.Acc.print

(** val wrong_dummy_toplevel_cont_name : string **)

let wrong_dummy_toplevel_cont_name = "wrong toplevel cont"

(** val empty : unit -> t coq_M **)

let empty _ =
  let wrong_dummy_toplevel_cont =
    (fun x__1 x__2 x__3 -> Continuation.create ?sort:x__1 ?name:x__2 x__3)
      None (Some wrong_dummy_toplevel_cont_name) ()
  in
  let res =
    { T.Acc.stack = [];
      T.Acc.map = Continuation.Map.empty;
      T.Acc.extra = Continuation.Map.empty;
      T.Acc.lifted_constants = Lifted_constant_state.empty;
      T.Acc.dummy_toplevel_cont = wrong_dummy_toplevel_cont
    }
  in
  res

(** val add_extra_params_and_args : Continuation.t ->
    Continuation_extra_params_and_args.t -> t -> t coq_M **)

let add_extra_params_and_args cont extra0 t0 =
  let extra1 =
    Continuation.Map.update cont
      (fun x ->
        match x with
        | Some _ -> Misc.fatal_errorf "Continuation extended a second time"
        | None -> Some extra0)
      t0.Flow_types.Acc.extra
  in
  (fun t extra -> { t with T.Acc.extra }) t0 extra1

(** val enter_continuation : Continuation.t -> bool -> bool ->
    Bound_parameters.t -> t -> t coq_M **)

let enter_continuation continuation0 recursive0 is_exn_handler0 params0 t0 =
  let parent_continuation0 =
    match t0.Flow_types.Acc.stack with
    | [] -> None
    | parent :: _ -> Some parent.Flow_types.Continuation_info.continuation
  in
  let used_in_handler0 =
    if not is_exn_handler0
    then Name_occurrences.empty
    else
      let first_param =
        Bound_parameter.var (List.hd (Bound_parameters.to_list params0))
      in
      Name_occurrences.singleton_variable first_param Name_mode.normal
  in
  let cont_info0 =
    { T.Continuation_info.continuation = continuation0;
      T.Continuation_info.recursive = recursive0;
      T.Continuation_info.is_exn_handler = is_exn_handler0;
      T.Continuation_info.params = params0;
      T.Continuation_info.parent_continuation = parent_continuation0;
      T.Continuation_info.used_in_handler = used_in_handler0;
      T.Continuation_info.bindings = Name.Map.empty;
      T.Continuation_info.direct_aliases = Variable.Map.empty;
      T.Continuation_info.mutable_let_prims_rev = [];
      T.Continuation_info.defined = Variable.Set.empty;
      T.Continuation_info.code_ids = Code_id.Map.empty;
      T.Continuation_info.value_slots = Value_slot.Map.empty;
      T.Continuation_info.apply_cont_args = Continuation.Map.empty
    }
  in
  (fun t stack -> { t with T.Acc.stack })
    t0
    (cont_info0 :: t0.Flow_types.Acc.stack)

(** val init_toplevel : Continuation.t -> Bound_parameters.t -> t coq_M **)

let init_toplevel dummy_toplevel_cont0 params0 =
  enter_continuation dummy_toplevel_cont0 false false params0
    ((fun t dummy_toplevel_cont -> { t with T.Acc.dummy_toplevel_cont })
       (empty ()) dummy_toplevel_cont0)

(** val exit_continuation : Continuation.t -> t -> t coq_M **)

let exit_continuation cont t0 =
  match t0.Flow_types.Acc.stack with
  | [] -> Misc.fatal_errorf "Empty stack of variable uses"
  | elt :: stack0 ->
    let { Flow_types.Continuation_info.continuation = continuation0;
          Flow_types.Continuation_info.recursive = _;
          Flow_types.Continuation_info.is_exn_handler = _;
          Flow_types.Continuation_info.params = _;
          Flow_types.Continuation_info.parent_continuation = _;
          Flow_types.Continuation_info.used_in_handler = _;
          Flow_types.Continuation_info.bindings = _;
          Flow_types.Continuation_info.direct_aliases = _;
          Flow_types.Continuation_info.mutable_let_prims_rev = _;
          Flow_types.Continuation_info.defined = _;
          Flow_types.Continuation_info.code_ids = _;
          Flow_types.Continuation_info.value_slots = _;
          Flow_types.Continuation_info.apply_cont_args = _
        } =
      elt
    in
    let () = assert (Continuation.equal cont continuation0) in
    let map0 = Continuation.Map.add cont elt t0.Flow_types.Acc.map in
    (fun t stack map -> { t with T.Acc.stack; map }) t0 stack0 map0

(** val update_top_of_stack : t -> (cont_info -> cont_info coq_M) -> t coq_M **)

let update_top_of_stack t0 f =
  match t0.Flow_types.Acc.stack with
  | [] -> Misc.fatal_errorf "Empty stack of variable uses"
  | elt :: stack0 -> (fun t stack -> { t with T.Acc.stack }) t0 (f elt :: stack0)

(** val record_defined_var : Variable.t -> t -> t coq_M **)

let record_defined_var var t0 =
  update_top_of_stack t0 (fun elt ->
      let defined0 =
        Variable.Set.add var elt.Flow_types.Continuation_info.defined
      in
      (fun t defined -> { t with T.Continuation_info.defined }) elt defined0)

(** val record_var_binding : Variable.t -> Name_occurrences.t -> bool -> t -> t
    coq_M **)

let record_var_binding var name_occurrences generate_phantom_lets t0 =
  update_top_of_stack t0 (fun elt ->
      let bindings0 =
        Name.Map.update (Name.var var)
          (fun x ->
            match x with
            | Some _ ->
              Misc.fatal_errorf
                "The following variable has been bound twice: %a" Variable.print
                var
            | None -> Some name_occurrences)
          elt.Flow_types.Continuation_info.bindings
      in
      let used_in_handler0 =
        if Variable.user_visible var && generate_phantom_lets
        then
          Name_occurrences.add_variable
            elt.Flow_types.Continuation_info.used_in_handler var
            Name_mode.phantom
        else elt.Flow_types.Continuation_info.used_in_handler
      in
      let defined0 =
        Variable.Set.add var elt.Flow_types.Continuation_info.defined
      in
      (fun t bindings used_in_handler defined ->
        { t with T.Continuation_info.bindings; used_in_handler; defined })
        elt bindings0 used_in_handler0 defined0)

(** val record_var_alias : Variable.t -> Simple.t -> t -> t coq_M **)

let record_var_alias var definition t0 =
  update_top_of_stack t0 (fun elt ->
      let direct_aliases0 =
        Variable.Map.update var
          (fun x ->
            match x with
            | Some _ ->
              Misc.fatal_errorf
                "The following variable has been bound twice: %a" Variable.print
                var
            | None -> Some definition)
          elt.Flow_types.Continuation_info.direct_aliases
      in
      let defined0 =
        Variable.Set.add var elt.Flow_types.Continuation_info.defined
      in
      (fun t direct_aliases defined ->
        { t with T.Continuation_info.direct_aliases; defined })
        elt direct_aliases0 defined0)

(** val record_ref_named : Named_rewrite_id.t -> Variable.t ->
    Flambda_primitive.t -> T.Mutable_prim.t -> t -> t coq_M **)

let record_ref_named named_rewrite_id0 bound_to original_prim0 prim0 t0 =
  update_top_of_stack t0 (fun cont_info0 ->
      let mutable_let_prim =
        { T.Mutable_let_prim.bound_var = bound_to;
          T.Mutable_let_prim.prim = prim0;
          T.Mutable_let_prim.original_prim = original_prim0;
          T.Mutable_let_prim.named_rewrite_id = named_rewrite_id0
        }
      in
      let mutable_let_prims_rev0 =
        mutable_let_prim
        :: cont_info0.Flow_types.Continuation_info.mutable_let_prims_rev
      in
      (fun t mutable_let_prims_rev ->
        { t with T.Continuation_info.mutable_let_prims_rev })
        cont_info0 mutable_let_prims_rev0)

(** val record_symbol_projection_aux : Variable.t -> Name_occurrences.t ->
    cont_info -> cont_info coq_M **)

let record_symbol_projection_aux var name_occurrences elt =
  let bindings0 =
    Name.Map.update (Name.var var)
      (fun original ->
        match original with
        | Some prior_occurences ->
          if Name_occurrences.equal prior_occurences name_occurrences
          then original
          else
            Misc.fatal_errorf
              "@[<v>The following projection has been bound to different \
               symbols:%a@ previously bound to:@ %a@ and now to@ %a@]"
              Variable.print var Name_occurrences.print prior_occurences
              Name_occurrences.print name_occurrences
        | None -> Some name_occurrences)
      elt.Flow_types.Continuation_info.bindings
  in
  (fun t bindings -> { t with T.Continuation_info.bindings }) elt bindings0

(** val record_symbol_projection : Variable.t -> Name_occurrences.t -> t -> t
    coq_M **)

let record_symbol_projection var name_occurrences t0 =
  update_top_of_stack t0 (record_symbol_projection_aux var name_occurrences)

(** val record_symbol_binding_aux : Symbol.t -> Name_occurrences.t -> cont_info
    -> cont_info coq_M **)

let record_symbol_binding_aux symbol name_occurrences elt =
  let bindings0 =
    Name.Map.update (Name.symbol symbol)
      (fun x ->
        match x with
        | Some _ ->
          Misc.fatal_errorf "The following symbol has been bound twice: %a"
            Symbol.print symbol
        | None -> Some name_occurrences)
      elt.Flow_types.Continuation_info.bindings
  in
  (fun t bindings -> { t with T.Continuation_info.bindings }) elt bindings0

(** val record_symbol_binding : Symbol.t -> Name_occurrences.t -> t -> t coq_M **)

let record_symbol_binding symbol name_occurrences t0 =
  update_top_of_stack t0 (record_symbol_binding_aux symbol name_occurrences)

(** val record_code_id_binding_aux : Code_id.t -> Name_occurrences.t ->
    cont_info -> cont_info coq_M **)

let record_code_id_binding_aux code_id name_occurrences elt =
  let code_ids0 =
    Code_id.Map.update code_id
      (fun x ->
        match x with
        | Some _ ->
          Misc.fatal_errorf "The following code_id has been bound twice: %a"
            Code_id.print code_id
        | None -> Some name_occurrences)
      elt.Flow_types.Continuation_info.code_ids
  in
  (fun t code_ids -> { t with T.Continuation_info.code_ids }) elt code_ids0

(** val record_code_id_binding : Code_id.t -> Name_occurrences.t -> t -> t coq_M
    **)

let record_code_id_binding code_id name_occurrences t0 =
  update_top_of_stack t0 (record_code_id_binding_aux code_id name_occurrences)

(** val record_value_slot_aux : Name.t -> Value_slot.t -> Name_occurrences.t ->
    cont_info -> cont_info coq_M **)

let record_value_slot_aux src value_slot dst elt =
  let value_slots0 =
    Value_slot.Map.update value_slot
      (fun x ->
        match x with
        | Some map0 ->
          Some
            (Name.Map.update src
               (fun x0 ->
                 match x0 with
                 | Some dst' -> Some (Name_occurrences.union dst dst')
                 | None -> Some dst)
               map0)
        | None -> Some (Name.Map.singleton src dst))
      elt.Flow_types.Continuation_info.value_slots
  in
  (fun t value_slots -> { t with T.Continuation_info.value_slots })
    elt value_slots0

(** val record_value_slot : Name.t -> Value_slot.t -> Name_occurrences.t -> t ->
    t coq_M **)

let record_value_slot src value_slot dst t0 =
  update_top_of_stack t0 (record_value_slot_aux src value_slot dst)

(** val add_used_in_current_handler : Name_occurrences.t -> t -> t coq_M **)

let add_used_in_current_handler name_occurrences t0 =
  update_top_of_stack t0 (fun elt ->
      let used_in_handler0 =
        Name_occurrences.union elt.Flow_types.Continuation_info.used_in_handler
          name_occurrences
      in
      (fun t used_in_handler -> { t with T.Continuation_info.used_in_handler })
        elt used_in_handler0)

(** val add_apply_conts : (Apply_cont_rewrite_id.t * Continuation.t) option ->
    (Apply_cont_rewrite_id.t * Exn_continuation.t) -> (_) Flambda_arity.t -> t
    -> t coq_M **)

let add_apply_conts result_cont exn_cont result_arity t0 =
  update_top_of_stack t0 (fun elt ->
      let add_func_result =
       fun cont rewrite_id result_arity0 extra_args apply_cont_args0 ->
        Continuation.Map.update cont
          (fun rewrite_map_opt ->
            let rewrite_map =
              Option.value rewrite_map_opt Apply_cont_rewrite_id.Map.empty
            in
            let rewrite_map0 =
              Apply_cont_rewrite_id.Map.update rewrite_id
                (fun x ->
                  match x with
                  | Some _ ->
                    Misc.fatal_errorf "Introducing a rewrite id twice %a"
                      Apply_cont_rewrite_id.print rewrite_id
                  | None ->
                    let map0 =
                      Numeric_types.Int.Map.of_list
                        (List.init result_arity0 (fun i ->
                             i, T.Cont_arg.Function_result))
                    in
                    let _, map1 =
                      List.fold_left
                        (fun pat pat' ->
                          let i, map1 = pat in
                          let extra_arg, _ = pat' in
                          let map2 =
                            Numeric_types.Int.Map.add i
                              (T.Cont_arg.Simple extra_arg) map1
                          in
                          i + 1, map2)
                        (1, map0) extra_args
                    in
                    Some map1)
                rewrite_map
            in
            Some rewrite_map0)
          apply_cont_args0
      in
      let apply_cont_args0 =
        let rewrite_id, exn_cont0 = exn_cont in
        add_func_result
          (Exn_continuation.exn_handler exn_cont0)
          rewrite_id 1
          (Exn_continuation.extra_args exn_cont0)
          elt.Flow_types.Continuation_info.apply_cont_args
      in
      let apply_cont_args1 =
        match result_cont with
        | Some p ->
          let rewrite_id, result_cont0 = p in
          add_func_result result_cont0 rewrite_id
            (Flambda_arity.cardinal_unarized result_arity)
            [] apply_cont_args0
        | None -> apply_cont_args0
      in
      (fun t apply_cont_args -> { t with T.Continuation_info.apply_cont_args })
        elt apply_cont_args1)

(** val add_apply_cont_args : Apply_cont_rewrite_id.t -> Continuation.t ->
    Simple.t list -> t -> t coq_M **)

let add_apply_cont_args rewrite_id cont arg_name_simples t0 =
  update_top_of_stack t0 (fun elt ->
      let apply_cont_args0 =
        Continuation.Map.update cont
          (fun rewrite_map_opt ->
            let rewrite_map =
              Option.value rewrite_map_opt Apply_cont_rewrite_id.Map.empty
            in
            let rewrite_map0 =
              Apply_cont_rewrite_id.Map.update rewrite_id
                (fun x ->
                  match x with
                  | Some _ ->
                    Misc.fatal_errorf "Introducing a rewrite id twice %a"
                      Apply_cont_rewrite_id.print rewrite_id
                  | None ->
                    let map0, _ =
                      List.fold_left
                        (fun pat arg_simple ->
                          let map0, i = pat in
                          let map1 =
                            Numeric_types.Int.Map.add i
                              (T.Cont_arg.Simple arg_simple) map0
                          in
                          map1, i + 1)
                        (Numeric_types.Int.Map.empty, 0)
                        arg_name_simples
                    in
                    Some map0)
                rewrite_map
            in
            Some rewrite_map0)
          elt.Flow_types.Continuation_info.apply_cont_args
      in
      (fun t apply_cont_args -> { t with T.Continuation_info.apply_cont_args })
        elt apply_cont_args0)

(** val get_block_and_constant_field : Simple.t -> Target_ocaml_int.t ->
    (Variable.t * int) option coq_M **)

let get_block_and_constant_field block field =
  Simple.pattern_match' block
    (fun var _ ->
      let field0 = Target_ocaml_int.to_int field in
      Some (var, field0))
    (fun _ _ -> None)
    (fun _ -> None)

(** val record_let_binding : Named_rewrite_id.t -> bool -> Bound_pattern.t ->
    Simplified_named.t -> t -> t coq_M **)

let record_let_binding rewrite_id generate_phantom_lets let_bound
    simplified_defining_expr t0 =
  let { Simplified_named.named = named0;
        Simplified_named.cost_metrics = _;
        Simplified_named.free_names = free_names0
      } =
    simplified_defining_expr
  in
  let record_var_bindings =
   fun t1 free_names1 ->
    Bound_pattern.fold_all_bound_vars let_bound t1 (fun t2 v ->
        record_var_binding (Bound_var.var v) free_names1 generate_phantom_lets
          t2)
  in
  match named0 with
  | Simplified_named.Simple simple ->
    let bound_var0 = Bound_pattern.must_be_singleton let_bound in
    let var = Bound_var.var bound_var0 in
    record_var_alias var simple t0
  | Simplified_named.Prim (original_prim0, _) -> (
    let bound_var0 = Bound_pattern.must_be_singleton let_bound in
    let var = Bound_var.var bound_var0 in
    match original_prim0 with
    | Flambda_primitive.Nullary _ ->
      if Flambda_primitive.at_most_generative_effects original_prim0
      then record_var_bindings t0 free_names0
      else
        let t1 = record_defined_var var t0 in
        add_used_in_current_handler free_names0 t1
    | Flambda_primitive.Unary (u, block) ->
      (fun f__1
        f__2
        f__3
        f__4
        f__5
        f__6
        f__7
        f__8
        f__9
        f__10
        f__11
        f__12
        f__13
        f__14
        f__15
        f__16
        f__17
        f__18
        f__19
        f__20
        f__21
        f__22
        f__23
        f__24
        f__25
        f__26
        f__27
        f__28
        f__29
        f__30
        f__31
        x__0
      ->
        match (x__0 : Flambda_primitive.unary_primitive) with
        | Flambda_primitive.Block_load { kind = x__1; mut = x__2; field = x__3 }
          ->
          f__1 x__1 x__2 x__3
        | Flambda_primitive.Duplicate_block { kind = x__1; alloc_region = x__2 }
          ->
          f__2 x__1 x__2
        | Flambda_primitive.Duplicate_array
            { kind = x__1;
              source_mutability = x__2;
              destination_mutability = x__3;
              alloc_region = x__4
            } ->
          f__3 x__1 x__2 x__3 x__4
        | Flambda_primitive.Is_int { variant_only = x__1 } -> f__4 x__1
        | Flambda_primitive.Is_null -> f__5 ()
        | Flambda_primitive.Get_tag -> f__6 ()
        | Flambda_primitive.Array_length x__1 -> f__7 x__1
        | Flambda_primitive.Bigarray_length { dimension = x__1 } -> f__8 x__1
        | Flambda_primitive.String_length x__1 -> f__9 x__1
        | Flambda_primitive.Int_as_pointer x__1 -> f__10 x__1
        | Flambda_primitive.Opaque_identity
            { middle_end_only = x__1; kind = x__2 } ->
          f__11 x__1 x__2
        | Flambda_primitive.Int_arith (x__1, x__2) -> f__12 x__1 x__2
        | Flambda_primitive.Float_arith (x__1, x__2) -> f__13 x__1 x__2
        | Flambda_primitive.Num_conv { src = x__1; dst = x__2 } ->
          f__14 x__1 x__2
        | Flambda_primitive.Boolean_not -> f__15 ()
        | Flambda_primitive.Reinterpret_64_bit_word x__1 -> f__16 x__1
        | Flambda_primitive.Reinterpret_boxed_vector -> f__17 ()
        | Flambda_primitive.Unbox_number x__1 -> f__18 x__1
        | Flambda_primitive.Box_number (x__1, x__2) -> f__19 x__1 x__2
        | Flambda_primitive.Untag_immediate -> f__20 ()
        | Flambda_primitive.Tag_immediate -> f__21 ()
        | Flambda_primitive.Project_function_slot
            { move_from = x__1; move_to = x__2 } ->
          f__22 x__1 x__2
        | Flambda_primitive.Project_value_slot
            { project_from = x__1; value_slot = x__2 } ->
          f__23 x__1 x__2
        | Flambda_primitive.Is_boxed_float -> f__24 ()
        | Flambda_primitive.Is_flat_float_array -> f__25 ()
        | Flambda_primitive.End_region { ghost = x__1 } -> f__26 x__1
        | Flambda_primitive.End_try_region { ghost = x__1 } -> f__27 x__1
        | Flambda_primitive.Obj_dup { alloc_region = x__1 } -> f__28 x__1
        | Flambda_primitive.Get_header -> f__29 ()
        | Flambda_primitive.Peek x__1 -> f__30 x__1
        | Flambda_primitive.Make_lazy { lazy_tag = x__1; alloc_region = x__2 }
          ->
          f__31 x__1 x__2)
        (fun bak mut field ->
          match get_block_and_constant_field block field with
          | Some p ->
            let block0, field0 = p in
            record_var_bindings
              (record_ref_named rewrite_id var original_prim0
                 ((fun (x__1, x__2, x__3, x__4) ->
                    (T.Mutable_prim.Block_load
                       { bak = x__1; mut = x__2; block = x__3; field = x__4 }
                      : T.Mutable_prim.t))
                    (bak, mut, block0, field0))
                 t0)
              Name_occurrences.empty
          | None -> record_var_bindings t0 free_names0)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          match Simple.must_be_var block with
          | Some p ->
            let v, _ = p in
            record_var_bindings
              (record_ref_named rewrite_id var original_prim0
                 (T.Mutable_prim.Is_int v) t0)
              Name_occurrences.empty
          | None -> record_var_bindings t0 free_names0)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          match Simple.must_be_var block with
          | Some p ->
            let v, _ = p in
            record_var_bindings
              (record_ref_named rewrite_id var original_prim0
                 (T.Mutable_prim.Get_tag v) t0)
              Name_occurrences.empty
          | None -> record_var_bindings t0 free_names0)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ -> t0)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        u
    | Flambda_primitive.Binary (b, block, value) ->
      (fun f__1
        f__2
        f__3
        f__4
        f__5
        f__6
        f__7
        f__8
        f__9
        f__10
        f__11
        f__12
        f__13
        f__14
        x__0
      ->
        match (x__0 : Flambda_primitive.binary_primitive) with
        | Flambda_primitive.Block_set { kind = x__1; init = x__2; field = x__3 }
          ->
          f__1 x__1 x__2 x__3
        | Flambda_primitive.Array_load (x__1, x__2, x__3) -> f__2 x__1 x__2 x__3
        | Flambda_primitive.String_or_bigstring_load (x__1, x__2) ->
          f__3 x__1 x__2
        | Flambda_primitive.Bigarray_load (x__1, x__2, x__3) ->
          f__4 x__1 x__2 x__3
        | Flambda_primitive.Phys_equal x__1 -> f__5 x__1
        | Flambda_primitive.Int_arith (x__1, x__2) -> f__6 x__1 x__2
        | Flambda_primitive.Int_shift (x__1, x__2) -> f__7 x__1 x__2
        | Flambda_primitive.Int_comp (x__1, x__2) -> f__8 x__1 x__2
        | Flambda_primitive.Float_arith (x__1, x__2) -> f__9 x__1 x__2
        | Flambda_primitive.Float_comp (x__1, x__2) -> f__10 x__1 x__2
        | Flambda_primitive.Bigarray_get_alignment x__1 -> f__11 x__1
        | Flambda_primitive.Atomic_load (x__1, x__2) -> f__12 x__1 x__2
        | Flambda_primitive.Poke x__1 -> f__13 x__1
        | Flambda_primitive.Read_offset (x__1, x__2) -> f__14 x__1 x__2)
        (fun bak _ field ->
          match get_block_and_constant_field block field with
          | Some p ->
            let block0, field0 = p in
            record_ref_named rewrite_id var original_prim0
              ((fun (x__1, x__2, x__3, x__4) ->
                 (T.Mutable_prim.Block_set
                    { bak = x__1; block = x__2; field = x__3; value = x__4 }
                   : T.Mutable_prim.t))
                 (bak, block0, field0, value))
              t0
          | None -> add_used_in_current_handler free_names0 t0)
        (fun _ _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        b
    | Flambda_primitive.Ternary (_, _, _, _) ->
      if Flambda_primitive.at_most_generative_effects original_prim0
      then record_var_bindings t0 free_names0
      else
        let t1 = record_defined_var var t0 in
        add_used_in_current_handler free_names0 t1
    | Flambda_primitive.Quaternary (_, _, _, _, _) ->
      if Flambda_primitive.at_most_generative_effects original_prim0
      then record_var_bindings t0 free_names0
      else
        let t1 = record_defined_var var t0 in
        add_used_in_current_handler free_names0 t1
    | Flambda_primitive.Variadic (v, fields) ->
      (fun f__1 f__2 f__3 f__4 x__0 ->
        match (x__0 : Flambda_primitive.variadic_primitive) with
        | Flambda_primitive.Begin_region { ghost = x__1 } -> f__1 x__1
        | Flambda_primitive.Begin_try_region { ghost = x__1 } -> f__2 x__1
        | Flambda_primitive.Make_block (x__1, x__2, x__3) -> f__3 x__1 x__2 x__3
        | Flambda_primitive.Make_array (x__1, x__2, x__3) -> f__4 x__1 x__2 x__3)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        (fun kind mut alloc_mode ->
          record_var_bindings
            (record_ref_named rewrite_id var original_prim0
               ((fun (x__1, x__2, x__3, x__4) ->
                  (T.Mutable_prim.Make_block
                     { kind = x__1;
                       mut = x__2;
                       alloc_mode = x__3;
                       fields = x__4
                     }
                    : T.Mutable_prim.t))
                  (kind, mut, alloc_mode, fields))
               t0)
            Name_occurrences.empty)
        (fun _ _ _ ->
          if Flambda_primitive.at_most_generative_effects original_prim0
          then record_var_bindings t0 free_names0
          else
            let t1 = record_defined_var var t0 in
            add_used_in_current_handler free_names0 t1)
        v)
  | Simplified_named.Set_of_closures (_, _) ->
    record_var_bindings t0 free_names0
  | Simplified_named.Rec_info _ -> record_var_bindings t0 free_names0

(** val record_lifted_function_slot_aux : Name_occurrences.t -> Simple.t
    Value_slot.Map.t -> 'a1 -> (Symbol.t * 'a2) -> cont_info -> cont_info coq_M
    **)

let record_lifted_function_slot_aux free_names0 value_slots0 _ pat elt =
  let symbol, _ = pat in
  let elt0 = record_symbol_binding_aux symbol free_names0 elt in
  Value_slot.Map.fold
    (fun value_slot simple elt1 ->
      record_value_slot_aux (Name.symbol symbol) value_slot
        (Simple.free_names simple) elt1)
    value_slots0 elt0

(** val record_lifted_constant_definition_aux : Name_occurrences.t -> cont_info
    -> Lifted_constant.Definition.t -> cont_info coq_M **)

let record_lifted_constant_definition_aux being_defined elt definition =
  (fun f__1 f__2 f__3 x__0 ->
    match (x__0 : Lifted_constant.Definition.descr) with
    | Lifted_constant.Definition.Code x__1 -> f__1 x__1
    | Lifted_constant.Definition.Set_of_closures
        { typing_env = x__1;
          closure_symbols_with_types = x__2;
          symbol_projections = x__3
        } ->
      f__2 x__1 x__2 x__3
    | Lifted_constant.Definition.Block_like
        { symbol = x__1;
          typing_env = x__2;
          ty = x__3;
          symbol_projections = x__4
        } ->
      f__3 x__1 x__2 x__3 x__4)
    (fun code_id ->
      record_code_id_binding_aux code_id
        (Name_occurrences.union being_defined
           (Lifted_constant.Definition.free_names definition))
        elt)
    (fun _ closure_symbols_with_types _ ->
      let expr = Lifted_constant.Definition.defining_expr definition in
      match Rebuilt_static_const.to_const expr with
      | Some t0 -> (
        match t0 with
        | Flambda.Code _ ->
          let free_names0 =
            Name_occurrences.union being_defined
              (Lifted_constant.Definition.free_names definition)
          in
          Function_slot.Lmap.fold
            (fun _ pat elt0 ->
              let symbol, _ = pat in
              record_symbol_binding_aux symbol free_names0 elt0)
            closure_symbols_with_types elt
        | Flambda.Deleted_code ->
          let free_names0 =
            Name_occurrences.union being_defined
              (Lifted_constant.Definition.free_names definition)
          in
          Function_slot.Lmap.fold
            (fun _ pat elt0 ->
              let symbol, _ = pat in
              record_symbol_binding_aux symbol free_names0 elt0)
            closure_symbols_with_types elt
        | Flambda.Static_const const ->
          let set_of_closures = Static_const.must_be_set_of_closures const in
          let free_names0 =
            Name_occurrences.union being_defined
              (Function_declarations.free_names
                 (Set_of_closures.function_decls set_of_closures))
          in
          let value_slots0 = Set_of_closures.value_slots set_of_closures in
          Function_slot.Lmap.fold
            (record_lifted_function_slot_aux free_names0 value_slots0)
            closure_symbols_with_types elt)
      | None ->
        let free_names0 =
          Name_occurrences.union being_defined
            (Lifted_constant.Definition.free_names definition)
        in
        Function_slot.Lmap.fold
          (fun _ pat elt0 ->
            let symbol, _ = pat in
            record_symbol_binding_aux symbol free_names0 elt0)
          closure_symbols_with_types elt)
    (fun symbol _ _ _ ->
      let free_names0 =
        Name_occurrences.union being_defined
          (Lifted_constant.Definition.free_names definition)
      in
      record_symbol_binding_aux symbol free_names0 elt)
    (Lifted_constant.Definition.descr definition)

(** val normalize_lifted_constant_aux : Lifted_constant.t -> cont_info ->
    cont_info coq_M **)

let normalize_lifted_constant_aux lifted_constant elt =
  let being_defined =
    let bound_static = Lifted_constant.bound_static lifted_constant in
    let symbols = Bound_static.symbols_being_defined bound_static in
    Symbol.Set.fold
      (fun symbol acc ->
        Name_occurrences.add_symbol acc symbol Name_mode.normal)
      symbols Name_occurrences.empty
  in
  let elt0 =
    Variable.Map.fold
      (fun var proj elt0 ->
        record_symbol_projection_aux var
          (Symbol_projection.free_names proj)
          elt0)
      (Lifted_constant.symbol_projections lifted_constant)
      elt
  in
  let elt1 =
    ListLabels.fold_left
      (record_lifted_constant_definition_aux being_defined)
      elt0
      (Lifted_constant.definitions lifted_constant)
  in
  elt1

(** val normalize_lifted_constants_aux : Lifted_constant_state.t -> cont_info ->
    cont_info coq_M **)

let normalize_lifted_constants_aux lifted_constants0 elt =
  Lifted_constant_state.fold lifted_constants0 elt (fun elt0 lifted_constant ->
      normalize_lifted_constant_aux lifted_constant elt0)

(** val record_lifted_constants : Lifted_constant_state.t -> t -> t coq_M **)

let record_lifted_constants lifted_constants0 t0 =
  (fun t lifted_constants -> { t with T.Acc.lifted_constants })
    t0
    (Lifted_constant_state.union lifted_constants0
       t0.Flow_types.Acc.lifted_constants)

(** val add_extra_args_to_call : EPA.Extra_arg.t list Or_invalid.t
    Apply_cont_rewrite_id.Map.t -> Apply_cont_rewrite_id.t -> T.Cont_arg.t
    Numeric_types.Int.Map.t -> T.Cont_arg.t Numeric_types.Int.Map.t option coq_M
    **)

let add_extra_args_to_call extra_args rewrite_id original_args =
  match Apply_cont_rewrite_id.Map.find_or_null rewrite_id extra_args with
  | Or_null.Null -> Some original_args
  | Or_null.This t0 -> (
    match t0 with
    | Or_invalid.Ok extra_args0 ->
      let args_acc =
        if Numeric_types.Int.Map.is_empty original_args
        then 0, Numeric_types.Int.Map.empty
        else
          let max_arg, _ = Numeric_types.Int.Map.max_binding original_args in
          max_arg + 1, original_args
      in
      let extra_args1 =
        List.map
          (fun x ->
            match x with
            | EPA.Extra_arg.Already_in_scope s -> T.Cont_arg.Simple s
            | EPA.Extra_arg.New_let_binding (v, prim0) ->
              T.Cont_arg.New_let_binding (v, Flambda_primitive.free_names prim0)
            | EPA.Extra_arg.New_let_binding_with_named_args (v, _) ->
              T.Cont_arg.New_let_binding (v, Name_occurrences.empty))
          extra_args0
      in
      let _, args =
        List.fold_left
          (fun pat extra_arg ->
            let i, args = pat in
            i + 1, Numeric_types.Int.Map.add i extra_arg args)
          args_acc extra_args1
      in
      Some args
    | Or_invalid.Invalid -> None)

(** val normalize_acc : Continuation.t Apply_cont_rewrite_id.Map.t
    Continuation.Map.t -> T.Acc.t -> T.Acc.t coq_M **)

let normalize_acc specialization_map t0 =
  let map0 =
    Continuation.Map.map
      (fun elt ->
        let apply_cont_args0 =
          Continuation.Map.fold
            (fun cont rewrite_ids acc ->
              match Continuation.Map.find_or_null cont specialization_map with
              | Or_null.Null -> Continuation.Map.add cont rewrite_ids acc
              | Or_null.This specialized_ids ->
                Apply_cont_rewrite_id.Map.fold
                  (fun id args acc0 ->
                    match
                      Apply_cont_rewrite_id.Map.find_or_null id specialized_ids
                    with
                    | Or_null.Null ->
                      Continuation_callsite_map.add cont id args acc0
                    | Or_null.This specialized ->
                      Continuation_callsite_map.add specialized id args acc0)
                  rewrite_ids acc)
            elt.Flow_types.Continuation_info.apply_cont_args
            Continuation.Map.empty
        in
        let apply_cont_args1 =
          Continuation.Map.filter_map
            (fun cont rewrite_ids ->
              let rewrite_ids0 =
                match
                  Continuation.Map.find_or_null cont t0.Flow_types.Acc.extra
                with
                | Or_null.Null -> rewrite_ids
                | Or_null.This epa ->
                  let extra_args = EPA.extra_args epa in
                  Apply_cont_rewrite_id.Map.filter_map
                    (add_extra_args_to_call extra_args)
                    rewrite_ids
              in
              if Apply_cont_rewrite_id.Map.is_empty rewrite_ids0
              then None
              else Some rewrite_ids0)
            apply_cont_args0
        in
        (fun t apply_cont_args ->
          { t with T.Continuation_info.apply_cont_args })
          elt apply_cont_args1)
      t0.Flow_types.Acc.map
  in
  let map1 =
    Continuation.Map.map
      (fun elt ->
        let defined0 =
          Continuation.Map.fold
            (fun callee_cont rewrite_ids defined0 ->
              match
                Continuation.Map.find_or_null callee_cont
                  t0.Flow_types.Acc.extra
              with
              | Or_null.Null -> defined0
              | Or_null.This epa ->
                Apply_cont_rewrite_id.Map.fold
                  (fun rewrite_id _ defined1 ->
                    match
                      Apply_cont_rewrite_id.Map.find_or_null rewrite_id
                        (EPA.extra_args epa)
                    with
                    | Or_null.Null -> defined1
                    | Or_null.This t1 -> (
                      match t1 with
                      | Or_invalid.Ok extra_args ->
                        let defined2 =
                          List.fold_left
                            (fun defined2 x ->
                              match x with
                              | EPA.Extra_arg.Already_in_scope _ -> defined2
                              | EPA.Extra_arg.New_let_binding (v, _) ->
                                Variable.Set.add v defined2
                              | EPA.Extra_arg.New_let_binding_with_named_args
                                  (v, _) ->
                                Variable.Set.add v defined2)
                            defined1 extra_args
                        in
                        defined2
                      | Or_invalid.Invalid -> defined1))
                  rewrite_ids defined0)
            elt.Flow_types.Continuation_info.apply_cont_args
            elt.Flow_types.Continuation_info.defined
        in
        (fun t defined -> { t with T.Continuation_info.defined }) elt defined0)
      map0
  in
  let map2 =
    Continuation.Map.fold
      (fun cont epa map2 ->
        let elt = Continuation.Map.find cont map2 in
        let elt0 =
          let params0 =
            Bound_parameters.append elt.Flow_types.Continuation_info.params
              (EPA.extra_params epa)
          in
          (fun t params -> { t with T.Continuation_info.params }) elt params0
        in
        Continuation.Map.add cont elt0 map2)
      t0.Flow_types.Acc.extra map1
  in
  let map3 =
    Continuation.Map.update t0.Flow_types.Acc.dummy_toplevel_cont
      (fun x ->
        match x with
        | Some elt ->
          Some
            (normalize_lifted_constants_aux t0.Flow_types.Acc.lifted_constants
               elt)
        | None ->
          Misc.fatal_errorf
            "Data_flow: missing continuation info for top-level expression")
      map2
  in
  (fun t map extra -> { t with T.Acc.map; extra })
    t0 map3 Continuation.Map.empty
