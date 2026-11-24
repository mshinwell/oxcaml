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
   middle_end/flambda2/rocq/simplify_port/flow/Flow_analysis.v, which follows
   middle_end/flambda2/simplify/flow/flow_analysis.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module T = Flow_types

let dominator_graph_ppf =
  lazy
    (let filename = "dom.dot" in
     let ch = open_out filename in
     let ppf = Format.formatter_of_out_channel ch in
     Format.fprintf ppf "digraph g {@\n";
     at_exit (fun () ->
         Format.fprintf ppf "@\n}@.";
         close_out ch);
     ppf)

let control_flow_graph_ppf =
  lazy
    (let filename = "flow.dot" in
     let ch = open_out filename in
     let ppf = Format.formatter_of_out_channel ch in
     Format.fprintf ppf "digraph g {@\n";
     at_exit (fun () ->
         Format.fprintf ppf "@\n}@.";
         close_out ch);
     ppf)

let dot_count = ref ~-1

open Port_abbreviations
open Port_monad

(** val print_graph : (int -> string -> Format.formatter -> 'a1 -> unit coq_M)
    -> string option -> Format.formatter lazy_t -> 'a1 -> unit coq_M **)

let print_graph print print_name lazy_ppf graph =
  match print_name with
  | Some print_name0 ->
    let () = incr dot_count in
    let ppf = Lazy.force lazy_ppf in
    print !dot_count print_name0 ppf graph
  | None -> ()

(** val analyze : bool option -> string option -> Target_system.Machine_width.t
    -> Continuation.t -> Continuation.t -> Flambda2_types.Code_age_relation.t ->
    Name_occurrences.t Or_unknown.t -> Code_id.Set.t -> Continuation.t
    Continuation_callsite_map.t -> T.Acc.t -> T.Flow_result.t coq_M **)

let analyze speculative print_name machine_width return_continuation
    exn_continuation code_age_relation used_value_slots code_ids_to_never_delete
    specialization_map t0 =
  let speculative0 =
    match speculative with Some speculative0 -> speculative0 | None -> false
  in
  (fun x__1 x__2 x__3 -> Profile.record_call ?accumulate:x__1 x__2 x__3)
    (Some true) "data_flow" (fun _ ->
      let () =
        if Flambda_features.dump_flow ()
        then
          Format.eprintf "PRESOURCE:@\nspec:%a@\n%a@\n@."
            (Continuation_callsite_map.print Continuation.print)
            specialization_map T.Acc.print t0
        else ()
      in
      let t1 = Flow_acc.normalize_acc specialization_map t0 in
      let { Flow_types.Acc.stack = stack0;
            Flow_types.Acc.map = map0;
            Flow_types.Acc.extra = _;
            Flow_types.Acc.lifted_constants = _;
            Flow_types.Acc.dummy_toplevel_cont = dummy_toplevel_cont0
          } =
        t1
      in
      let () = assert (match stack0 with [] -> true | _ :: _ -> false) in
      let () =
        assert (
          not
            (String.equal
               (Continuation.name dummy_toplevel_cont0)
               Flow_acc.wrong_dummy_toplevel_cont_name))
      in
      let () =
        if Flambda_features.dump_flow ()
        then Format.eprintf "SOURCE:@\n%a@\n@." T.Acc.print t1
        else ()
      in
      let deps =
        Data_flow_graph.create return_continuation exn_continuation
          code_age_relation used_value_slots code_ids_to_never_delete map0
      in
      let () =
        if Flambda_features.dump_flow ()
        then Format.eprintf "/// graph@\n%a@\n@." Data_flow_graph.print deps
        else ()
      in
      let dead_variable_result = Data_flow_graph.required_names deps in
      let dom_graph =
        Dominator_graph.create
          dead_variable_result.Flow_types.Data_flow_result.required_names
          return_continuation exn_continuation map0
      in
      let aliases = Dominator_graph.dominator_analysis dom_graph in
      let aliases_kind0 = Dominator_graph.aliases_kind dom_graph aliases in
      let () =
        if Flambda_features.dump_flow ()
        then
          print_graph
            (fun ctx print_name0 ppf graph ->
              Dominator_graph.Dot.print ctx print_name0 aliases ppf graph)
            print_name dominator_graph_ppf dom_graph
        else ()
      in
      let control = Control_flow_graph.create dummy_toplevel_cont0 t1 in
      let reference_analysis =
        Mutable_unboxing.create aliases dom_graph t1 control
          dead_variable_result.Flow_types.Data_flow_result.required_names
          return_continuation exn_continuation machine_width
      in
      let pp_node = Mutable_unboxing.pp_node reference_analysis in
      let reference_result, unboxed_blocks =
        Mutable_unboxing.make_result reference_analysis
      in
      let continuation_parameters0 =
        Control_flow_graph.compute_continuation_extra_args_for_aliases
          speculative0
          dead_variable_result.Flow_types.Data_flow_result.required_names t1
          unboxed_blocks aliases control
      in
      let () =
        if Flambda_features.dump_flow ()
        then
          print_graph
            (fun ctx print_name0 ppf graph ->
              (fun x__1 x__2 x__3 x__4 x__5 x__6 x__7 x__8 x__9 ->
                Control_flow_graph.Dot.print x__1 x__2 x__3 x__4 x__5 x__6
                  ?pp_node:x__7 x__8 x__9)
                ctx t1 print_name0 ppf return_continuation exn_continuation
                (Some pp_node) continuation_parameters0 graph)
            print_name control_flow_graph_ppf control
        else ()
      in
      let required_names_after_ref_reference_analysis =
        Continuation.Map.fold
          (fun _ epa required_names0 ->
            let params =
              Bound_parameters.var_set
                (Continuation_extra_params_and_args.extra_params epa)
            in
            Name.Set.union required_names0 (Name.set_of_var_set params))
          reference_result.Flow_types.Mutable_unboxing_result.additional_epa
          dead_variable_result.Flow_types.Data_flow_result.required_names
      in
      let result =
        { T.Flow_result.data_flow_result =
            { T.Data_flow_result.required_names =
                required_names_after_ref_reference_analysis;
              T.Data_flow_result.reachable_code_ids =
                dead_variable_result
                  .Flow_types.Data_flow_result.reachable_code_ids
            };
          T.Flow_result.aliases_result =
            { T.Alias_result.aliases_kind = aliases_kind0;
              T.Alias_result.continuation_parameters = continuation_parameters0
            };
          T.Flow_result.mutable_unboxing_result = reference_result
        }
      in
      let () =
        if Flambda_features.dump_flow ()
        then Format.eprintf "/// result@\n%a@\n@." T.Flow_result.print result
        else ()
      in
      result)

(** val did_perform_mutable_unboxing : T.Flow_result.t -> bool coq_M **)

let did_perform_mutable_unboxing result =
  result.Flow_types.Flow_result.mutable_unboxing_result
    .Flow_types.Mutable_unboxing_result.did_unbox_a_mutable_block
  || Named_rewrite_id.Map.exists
       (fun _ named_rewrite ->
         let (Named_rewrite.Prim_rewrite t0) = named_rewrite in
         (fun f__1 f__2 f__3 x__0 ->
           match (x__0 : Named_rewrite.Prim_rewrite.t) with
           | Named_rewrite.Prim_rewrite.Remove_prim -> f__1 ()
           | Named_rewrite.Prim_rewrite.Invalid x__1 -> f__2 x__1
           | Named_rewrite.Prim_rewrite.Replace_by_binding
               { var = x__1; bound_to = x__2 } ->
             f__3 x__1 x__2)
           (fun _ -> false)
           (fun _ -> true)
           (fun _ _ -> true)
           t0)
       result.Flow_types.Flow_result.mutable_unboxing_result
         .Flow_types.Mutable_unboxing_result.let_rewrites

(** val added_useful_alias_in_loop : Flambda2_types.Typing_env.t -> T.Acc.t ->
    T.Flow_result.t -> bool coq_M **)

let added_useful_alias_in_loop typing_env acc result =
  Seq.exists2
    (fun pat pat' ->
      let k, continuation_info = pat in
      let k', continuation_param_aliases = pat' in
      let () =
        if not (Continuation.equal k k')
        then
          Misc.fatal_errorf
            "[Flow Analysis]: Mismatch beetween continuation maps for source \
             info and continuation params alias result"
        else ()
      in
      continuation_info.Flow_types.Continuation_info.recursive
      && Variable.Lmap.exists
           (fun _ bound_to ->
             Simple.pattern_match' bound_to
               (fun _ _ -> false)
               (fun sym _ ->
                 let ty =
                   Flambda2_types.Typing_env.find typing_env (Name.symbol sym)
                     (Some Flambda_kind.value)
                 in
                 not (Flambda2_types.is_unknown typing_env ty))
               (fun _ -> true))
           continuation_param_aliases
             .Flow_types.Continuation_param_aliases.lets_to_introduce)
    (Continuation.Map.to_seq acc.Flow_types.Acc.map)
    (Continuation.Map.to_seq
       result.Flow_types.Flow_result.aliases_result
         .Flow_types.Alias_result.continuation_parameters)

let analyze ?speculative ?print_name machine_width return_continuation
    exn_continuation code_age_relation used_value_slots code_ids_to_never_delete
    specialization_map t =
  analyze speculative print_name machine_width return_continuation
    exn_continuation code_age_relation used_value_slots code_ids_to_never_delete
    specialization_map t
