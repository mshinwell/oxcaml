(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2022 OCamlPro SAS                                    *)
(*   Copyright 2014--2022 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* This file follows
   middle_end/flambda2/simplify/simplify_set_of_closures_context.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Simplify_import.
From SimplifyPort.decl Require Alloc_mode Bound_name Code_id Code_metadata
  Code_or_metadata Flambda_features Function_declarations Function_slot
  Inlining_history Inlining_report Inlining_state List Name Option
  Or_unknown Rec_info_expr Simple Simplify_common Value_slot Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(*OCAML
open! Simplify_import
OCAML*)

(* 19-28 *)
(* PORT-GAP(loose): 60-69 and 76-78, the seven functions that only read the
   field of their name ([simplify_function_body], [dacc_prior_to_sets],
   [dacc_inside_functions], [old_to_new_code_ids_all_sets],
   [closure_bound_names_inside_functions_all_sets],
   [previously_free_depth_variables], [single_set_of_size_one]) are the
   projections of this record, which Rocq prints here and not at their
   lines. *)
Record t : Type := {
  dacc_prior_to_sets : DA.t;
  simplify_function_body : Simplify_common.simplify_function_body;
  dacc_inside_functions : DA.t;
  closure_bound_names_inside_functions_all_sets :
    list (Function_slot.Map.t Bound_name.t);
  old_to_new_code_ids_all_sets : Code_id.Map.t Code_id.t;
  previously_free_depth_variables : Variable_.Set_.t;
  single_set_of_size_one : bool
}.

(* 30-32. In the compiler: [?new_code_id ~rec_info old_code_id];
   [Option.value new_code_id ~default:old_code_id]. *)
Definition function_decl_type (new_code_id : option Code_id.t)
    (rec_info : T.t) (old_code_id : Code_id.t)
    : M (Or_unknown.t T.Function_type.t) :=
  let* code_id := Option.value new_code_id old_code_id in
  let! tmp1 := T.Function_type.create code_id rec_info in
  ret (Or_unknown.Known tmp1).

(* 34-58. In the compiler: [dacc ~all_code ~simplify_function_body]. *)
Definition create_for_static_stub (dacc : DA.t)
    (all_code : Code_id.Map.t Code.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    : M t :=
  let* dacc_inside_functions :=
    (* We ensure that inlining cannot happen inside the code of stubs. This
       is to avoid compile-time performance problems where large functions
       (or other stubs) might get inlined repeatedly into stubs. One place
       where this was seen was code generated for labelled / optional
       argument application when there are a lot of parameters. *)
    DA.map_denv dacc
      (fun denv =>
        (* 45-48, the compiler's note (pchambart): we are not entering a set
           of closure, this function code creates a context to simplify a
           function while looking at the let code rather than the set of
           closure. We should rename this [DE.enter_set_of_closures]
           function. *)
        let! tmp1 := DE.enter_set_of_closures denv in
        let! tmp2 := DE.enter_stub_function tmp1 in
        Code_id.Map.fold
          (fun code_id code denv => DE.define_code denv code_id code)
          all_code tmp2)
  in
  ret
    {| dacc_prior_to_sets := dacc;
       simplify_function_body := simplify_function_body;
       dacc_inside_functions := dacc_inside_functions;
       closure_bound_names_inside_functions_all_sets := [];
       old_to_new_code_ids_all_sets := Code_id.Map.empty;
       previously_free_depth_variables := Variable_.Set_.empty;
       single_set_of_size_one := false
    |}.

(* 60: [simplify_function_body], 62: [dacc_prior_to_sets], 64:
   [dacc_inside_functions], 66: [old_to_new_code_ids_all_sets], and 68-69:
   [closure_bound_names_inside_functions_all_sets], are the projections
   above. *)

(* 71-74 *)
Definition closure_bound_names_inside_functions_exactly_one_set
    (t : Simplify_set_of_closures_context.t)
    : M (Function_slot.Map.t Bound_name.t) :=
  match t.(closure_bound_names_inside_functions_all_sets) with
  | [closure_bound_names_inside] => ret closure_bound_names_inside
  | [] | _ :: _ :: _ => fatal_error "Only one set of closures was expected"
  end.

(* 76: [previously_free_depth_variables], and 78: [single_set_of_size_one],
   are the projections above. *)

(* 80-87 *)
Definition stub_can_be_simplified (denv : DE.t) : M bool :=
  (* Stubs can only be simplified with "-flambda2-simplify-stubs". We want
     to avoid stub resimplifications because it's costly and often useless.
     The most problematic case are nested stub definitions. To avoid going
     through those multiple times, we don't simplify stub definitions while
     inlining stubs (stub depth > 0) *)
  let! tmp1 := Flambda_features.simplify_stubs tt in
  and_then tmp1
    (let! tmp2 := DE.get_inlining_state denv in
     let! tmp3 := Inlining_state.stub_depth tmp2 in
     ret (tmp3 =? 0)).

(* 89-92 *)
Definition function_can_be_simplified (denv : DE.t)
    (code : Code_or_metadata.t) : M bool :=
  let! tmp1 := Code_or_metadata.code_present code in
  and_then tmp1
    (let! tmp2 := Code_or_metadata.code_metadata code in
     let! tmp3 := Code_metadata.stub tmp2 in
     or_else (negb tmp3) (stub_can_be_simplified denv)).

(* 94-175. In the compiler: [~denv ~all_sets_of_closures
   ~closure_bound_names_all_sets ~value_slot_types_inside_functions_all_sets
   ~old_to_new_code_ids_all_sets]. *)
Definition compute_closure_types_inside_functions (denv : DE.t)
    (all_sets_of_closures : list (Set_of_closures.t * Alloc_mode.For_types.t))
    (closure_bound_names_all_sets : list (Function_slot.Map.t Bound_name.t))
    (value_slot_types_inside_functions_all_sets : list (Value_slot.Map.t T.t))
    (old_to_new_code_ids_all_sets : Code_id.Map.t Code_id.t)
    : M (list (Function_slot.Map.t Bound_name.t)
         * list (Function_slot.Map.t T.t)) :=
  (* There is explicit recursion in closure types, meaning that aliases must
     be used in order to build the necessary types. In the case where the
     set of closures will be lifted (note that the lifting decision has
     already been made by this point), then the names used for the aliases
     are just the closure symbols. In the non-lifted case we just need a
     list of variables, so we reuse the "closure bound names". If any of
     these variables escape in the function result types they will be
     captured by the name abstraction used there. *)
  let* closure_types_via_aliases_all_sets :=
    List.map
      (fun closure_bound_names_inside =>
        Function_slot.Map.map
          (fun name =>
            let! tmp1 := Bound_name.name name in
            let! tmp2 := Simple.name tmp1 in
            T.alias_type_of K.value tmp2)
          closure_bound_names_inside)
      closure_bound_names_all_sets
  in
  (* 114-174. [tmp1] and [tmp2] are used after the functions that follow
     them: the temporaries inside those functions begin at [tmp2] and
     [tmp3]. *)
  let* closure_types_inside_functions :=
    let! tmp1 :=
      List.combine closure_types_via_aliases_all_sets
        value_slot_types_inside_functions_all_sets
    in
    List.map2
      (fun '(set_of_closures, alloc_mode)
           '(closure_types_via_aliases, value_slot_types_inside_function) =>
        let* function_decls :=
          Set_of_closures.function_decls set_of_closures
        in
        let* all_function_slots_in_set :=
          let! tmp2 := Function_declarations.funs function_decls in
          Function_slot.Map.mapi
            (fun function_slot
                 (old_code_id :
                   Function_declarations.code_id_in_function_declaration) =>
              match old_code_id with
              | decl.Function_declarations.Deleted _ _ =>
                ret Or_unknown.Unknown
              | decl.Function_declarations.Code_id old_code_id _ =>
                match_exn
                  (fun _ => DE.find_code_exn denv old_code_id)
                  Not_found
                  (fun _ => ret Or_unknown.Unknown)
                  (fun code_or_metadata =>
                    let* new_code_id :=
                      (* The types of the functions involved should
                         reference the _new_ code IDs (where such exist),
                         so that direct recursive calls can be compiled
                         straight to the new code. *)
                      let! tmp3 :=
                        function_can_be_simplified denv code_or_metadata
                      in
                      if tmp3
                      then
                        Code_id.Map.find old_code_id
                          old_to_new_code_ids_all_sets
                      else ret old_code_id
                    in
                    let* rec_info :=
                      (* From inside their own bodies, every function in
                         the set currently being defined has an unknown
                         recursion depth *)
                      T.unknown K.rec_info
                    in
                    let* code_metadata :=
                      Code_or_metadata.code_metadata code_or_metadata
                    in
                    (* 149-155: [a |> f b] is [f b a]. *)
                    let* '(absolute_history, _relative_history) :=
                      let! tmp3 := DE.inlining_history_tracker denv in
                      let! tmp4 := Function_slot.name function_slot in
                      let! tmp5 :=
                        Code_metadata.relative_history code_metadata
                      in
                      let! tmp6 := Code_metadata.dbg code_metadata in
                      Inlining_history.Tracker.fundecl tmp6 tmp5 tmp4 tmp3
                    in
                    (* 157-160 *)
                    (let! tmp3 :=
                       Code_metadata.inlining_decision code_metadata
                     in
                     let! tmp4 := DE.are_rebuilding_terms denv in
                     Inlining_report.record_decision_at_function_definition
                       absolute_history code_metadata
                       Inlining_report.Pass.Before_simplify tmp4 tmp3) ;;
                    function_decl_type (Some new_code_id) rec_info
                      old_code_id)
              end)
            tmp2
        in
        Function_slot.Map.mapi
          (fun function_slot _function_decl =>
            T.exactly_this_closure function_slot all_function_slots_in_set
              closure_types_via_aliases value_slot_types_inside_function
              alloc_mode)
          all_function_slots_in_set)
      all_sets_of_closures tmp1
  in
  ret (closure_bound_names_all_sets, closure_types_inside_functions).

(* 177-217. In the compiler: [denv_inside_functions
   ~closure_bound_names_inside_functions_all_sets
   ~closure_types_inside_functions_all_sets]. *)
Definition bind_closure_types_inside_functions (denv_inside_functions : DE.t)
    (closure_bound_names_inside_functions_all_sets :
      list (Function_slot.Map.t Bound_name.t))
    (closure_types_inside_functions_all_sets :
      list (Function_slot.Map.t T.t)) : M DE.t :=
  let* denv_inside_functions :=
    List.fold_left
      (fun denv closure_bound_names_inside =>
        Function_slot.Map.fold
          (fun _function_slot bound_name denv =>
            let* name := Bound_name.name bound_name in
            let* in_types :=
              let! tmp1 := Bound_name.is_symbol bound_name in
              ret (negb tmp1)
            in
            let* bound_name :=
              Bound_name.create name
                (if in_types then NM.in_types else NM.normal)
            in
            DE.define_name denv bound_name K.value)
          closure_bound_names_inside denv)
      denv_inside_functions closure_bound_names_inside_functions_all_sets
  in
  (* 195-217 *)
  List.fold_left2
    (fun denv closure_bound_names_inside_functions_one_set
         closure_types_inside_functions_one_set =>
      Function_slot.Map.fold
        (fun function_slot closure_type denv =>
          match_exn
            (fun _ =>
              Function_slot.Map.find function_slot
                closure_bound_names_inside_functions_one_set)
            Not_found
            (fun _ =>
              (* PORT-GAP(papp): [Function_slot.Map.print] is given its
                 first argument only. *)
              let! tmp1 := papp1 Function_slot.Map.print Bound_name.print in
              fatal_errorf4
                "No closure name for function slot %a.@ closure_bound_names_inside_functions_one_set = %a."
                Function_slot.print function_slot tmp1
                closure_bound_names_inside_functions_one_set)
            (fun bound_name =>
              let! tmp1 := Bound_name.name bound_name in
              DE.add_equation_on_name denv tmp1 closure_type))
        closure_types_inside_functions_one_set denv)
    denv_inside_functions closure_bound_names_inside_functions_all_sets
    closure_types_inside_functions_all_sets.

(* 219-244. In the compiler: [denv ~all_sets_of_closures]. *)
Definition compute_old_to_new_code_ids_all_sets (denv : DE.t)
    (all_sets_of_closures : list (Set_of_closures.t * Alloc_mode.For_types.t))
    : M (Code_id.Map.t Code_id.t) :=
  List.fold_left
    (fun old_to_new_code_ids_all_sets '(set_of_closures, _alloc_mode) =>
      let* function_decls := Set_of_closures.function_decls set_of_closures in
      (* [tmp1] is used after the function: the temporaries inside the
         function begin at [tmp2]. *)
      let! tmp1 := Function_declarations.funs function_decls in
      Function_slot.Map.fold
        (fun _
             (old_code_id :
               Function_declarations.code_id_in_function_declaration)
             old_to_new_code_ids =>
          match old_code_id with
          | decl.Function_declarations.Deleted _ _ => ret old_to_new_code_ids
          | decl.Function_declarations.Code_id old_code_id _ =>
            let* code :=
              try_with
                (fun _ => DE.find_code_exn denv old_code_id)
                Not_found
                (fun _ =>
                  fatal_errorf2 "Missing code for %a" Code_id.print
                    old_code_id)
            in
            let! tmp2 := function_can_be_simplified denv code in
            if tmp2
            then
              let* new_code_id := Code_id.rename old_code_id in
              Code_id.Map.add old_code_id new_code_id old_to_new_code_ids
            else ret old_to_new_code_ids
          end)
        tmp1 old_to_new_code_ids_all_sets)
    Code_id.Map.empty all_sets_of_closures.

(* 246-261. In the compiler: [denv ~old_to_new_code_ids_all_sets]. *)
Definition bind_existing_code_to_new_code_ids (denv : DE.t)
    (old_to_new_code_ids_all_sets : Code_id.Map.t Code_id.t) : M DE.t :=
  Code_id.Map.fold
    (fun old_code_id new_code_id denv =>
      match_exn
        (fun _ => DE.find_code_exn denv old_code_id)
        Not_found
        (fun _ => ret denv)
        (fun code =>
          let! tmp1 := function_can_be_simplified denv code in
          if tmp1
          then
            (* 254-258: [a |> f b] is [f b a]. *)
            let* code :=
              let! tmp1 := Code_or_metadata.get_code code in
              let! tmp2 := Code.with_newer_version_of (Some old_code_id) tmp1 in
              Code.with_code_id new_code_id tmp2
            in
            DE.define_code denv new_code_id code
          else ret denv))
    old_to_new_code_ids_all_sets denv.

(* 263-326. In the compiler: [~typing_env ~denv_inside_functions
   ~value_slot_types_all_sets]. *)
Definition compute_and_erase_depth_variables (typing_env : TE.t)
    (denv_inside_functions : DE.t)
    (value_slot_types_all_sets : list (Value_slot.Map.t T.t))
    : M (DE.t * Variable_.Set_.t) :=
  (* The purpose of the code below is to compute the set of depth variables
     that appear in value slots and might end up free in the body of the
     function through simplification of the [Project_value_slot] primitive.
     This would be wrong, because these depth variables are not accessible
     from the closure (they are now bound with [In_types] name mode, and
     cannot appear in terms). See discussion below for details.

     If the "erase in-types depth variables" option is set, we don't have to
     do anything here: instead, any depth variable with [In_types] that is
     actually accessed during the simplification of the function's body will
     be replaced with [Rec_info_expr.do_not_inline] in by
     [simplify_rec_info_expr]. This is important for performance, as the
     computation of the transitive free names below can be extremely
     expensive (upwards of 5% of the total compilation time in pathological
     cases).

     The compiler's note for some day (lmaurer): It would be better to
     propagate depth variables into closures properly, as this would allow
     things like unrolling [Seq.map] where the recursive call goes through a
     closure. For the moment, we often just stop unrolling cold in that
     situation. (It's important that we use [Rec_info_expr.do_not_inline]
     here so that we don't start unrolling, since without propagating the
     rec info into the closure, we don't know when to stop unrolling.)

     mshinwell: Leo and I have discussed allowing In_types variables in
     closures, which should cover this case, if we allowed such variables to
     be of kinds other than [Value]. *)
  let! tmp1 := Flambda_features.erase_in_types_depth_variables tt in
  if tmp1
  then ret (denv_inside_functions, Variable_.Set_.empty)
  else
    (* 294-314: [a |> f b] is [f b a]. [tmp1] and [tmp2] are used after the
       functions that follow them: the temporaries inside those functions
       begin at [tmp2] and [tmp3]. *)
    let* free_depth_variables :=
      let! tmp1 :=
        List.concat_map
          (fun value_slot_types =>
            let! tmp2 :=
              Value_slot.Map.mapi
                (fun _value_slot ty =>
                  let* vars := TE.free_names_transitive typing_env ty in
                  NO.fold_variables vars Variable_.Set_.empty
                    (fun free_depth_variables var =>
                      let* ty :=
                        let! tmp3 := Name.var var in
                        let! tmp4 := DE.typing_env denv_inside_functions in
                        TE.find tmp4 tmp3 None
                      in
                      let! tmp3 := T.kind ty in
                      match tmp3 with
                      | K.Rec_info =>
                        Variable_.Set_.add var free_depth_variables
                      | K.Value | K.Naked_number _ | K.Region =>
                        ret free_depth_variables
                      end))
                value_slot_types
            in
            Value_slot.Map.data tmp2)
          value_slot_types_all_sets
      in
      Variable_.Set_.union_list tmp1
    in
    (* Pretend that any depth variables appearing free in the closure
       elements are bound to "never inline anything" in the function. This
       ensures that in-types depth variables do not end up in terms. *)
    let* denv_inside_functions :=
      Variable_.Set_.fold
        (fun dv env_inside_functions =>
          let* name := Name.var dv in
          let! tmp1 := T.this_rec_info Rec_info_expr.do_not_inline in
          DE.add_equation_on_name env_inside_functions name tmp1)
        free_depth_variables denv_inside_functions
    in
    ret (denv_inside_functions, free_depth_variables).

(* 328-375. In the compiler: [~dacc_prior_to_sets ~simplify_function_body
   ~all_sets_of_closures ~closure_bound_names_all_sets
   ~value_slot_types_all_sets]. *)
Definition create (dacc_prior_to_sets : DA.t)
    (simplify_function_body : Simplify_common.simplify_function_body)
    (all_sets_of_closures : list (Set_of_closures.t * Alloc_mode.For_types.t))
    (closure_bound_names_all_sets : list (Function_slot.Map.t Bound_name.t))
    (value_slot_types_all_sets : list (Value_slot.Map.t T.t)) : M t :=
  let* denv := DA.denv dacc_prior_to_sets in
  (* 331-337: [a |> f] is [f a]. *)
  let* denv_inside_functions :=
    let! tmp1 := DE.enter_set_of_closures denv in
    (* Even if we are not rebuilding terms we should always rebuild them for
       local functions. The type of a function is dependent on its term and
       not knowing it prohibits us from inlining it. *)
    DE.set_rebuild_terms tmp1
  in
  (* 338-341 *)
  let* '(denv_inside_functions, previously_free_depth_variables) :=
    let! tmp1 := DE.typing_env denv in
    compute_and_erase_depth_variables tmp1 denv_inside_functions
      value_slot_types_all_sets
  in
  let* old_to_new_code_ids_all_sets :=
    compute_old_to_new_code_ids_all_sets denv all_sets_of_closures
  in
  (* 345-351 *)
  let* '(closure_bound_names_inside_functions_all_sets,
         closure_types_inside_functions_all_sets) :=
    compute_closure_types_inside_functions denv all_sets_of_closures
      closure_bound_names_all_sets value_slot_types_all_sets
      old_to_new_code_ids_all_sets
  in
  (* 352-359: [a |> f b] is [f b a]. *)
  let* dacc_inside_functions :=
    let! tmp1 :=
      bind_existing_code_to_new_code_ids denv_inside_functions
        old_to_new_code_ids_all_sets
    in
    let! tmp2 :=
      bind_closure_types_inside_functions tmp1
        closure_bound_names_inside_functions_all_sets
        closure_types_inside_functions_all_sets
    in
    DA.with_denv dacc_prior_to_sets tmp2
  in
  (* 360-367 *)
  let* single_set_of_size_one :=
    match all_sets_of_closures with
    | [(set_of_closures, _)] =>
      let! tmp1 := Set_of_closures.function_decls set_of_closures in
      let! tmp2 := Function_declarations.funs_in_order tmp1 in
      Function_slot.Lmap.is_singleton tmp2
    | _ => ret false
    end
  in
  ret
    {| dacc_prior_to_sets := dacc_prior_to_sets;
       simplify_function_body := simplify_function_body;
       dacc_inside_functions := dacc_inside_functions;
       closure_bound_names_inside_functions_all_sets :=
         closure_bound_names_inside_functions_all_sets;
       old_to_new_code_ids_all_sets := old_to_new_code_ids_all_sets;
       previously_free_depth_variables := previously_free_depth_variables;
       single_set_of_size_one := single_set_of_size_one
    |}.

(* PORT-GAP(verbatim): 30, the optional argument [?new_code_id] of
   [function_decl_type]. *)
(*OCAML-END
let function_decl_type ?new_code_id rec_info old_code_id =
  function_decl_type new_code_id rec_info old_code_id
OCAML-END*)
