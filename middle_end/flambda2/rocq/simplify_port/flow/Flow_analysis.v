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

(* This file follows middle_end/flambda2/simplify/flow/flow_analysis.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order) is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameters Code_id Continuation
  Continuation_callsite_map Continuation_extra_params_and_args
  Control_flow_graph Data_flow_graph Dominator_graph Flambda2_types
  Flambda_features Flambda_kind Flow_acc Flow_types Format Mutable_unboxing
  Name Name_occurrences Named_rewrite Named_rewrite_id Or_unknown Profile Seq
  Simple Stdlib_ String Target_system Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
From SimplifyPort.abbrev.flow_analysis Require Import Port_abbreviations.
(*OCAML
module T = Flow_types
OCAML*)

(* debugging code *)

(* PORT-GAP(init): 19-28, a lazy value that opens a file and registers a
   function for the exit of the program when it is forced: the compiler's
   text. *)
(*OCAML
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
OCAML*)
Parameter dominator_graph_ppf : lazy_t Format.formatter.
Extract Inlined Constant dominator_graph_ppf => "dominator_graph_ppf".

(* PORT-GAP(init): 30-39, as above. *)
(*OCAML
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
OCAML*)
Parameter control_flow_graph_ppf : lazy_t Format.formatter.
Extract Inlined Constant control_flow_graph_ppf => "control_flow_graph_ppf".

(* PORT-GAP(init): 41, a reference that the module makes when it starts. *)
(*OCAML
let dot_count = ref ~-1
OCAML*)
Parameter dot_count : ref int.
Extract Inlined Constant dot_count => "dot_count".

(* 43-49 *)
Definition print_graph {G : Type}
    (print : int -> string -> Format.formatter -> G -> M unit)
    (print_name : option string) (lazy_ppf : lazy_t Format.formatter)
    (graph : G) : M unit :=
  match print_name with
  | None => ret tt
  | Some print_name =>
    Stdlib_.incr dot_count ;;
    let* ppf := force lazy_ppf in
    let! tmp1 := get dot_count in
    print tmp1 print_name ppf graph
  end.

(* analysis *)

(* 53-149. [speculative] and [print_name] are optional arguments in the
   compiler: by place here, and the compiler's function is at the end of
   the file. *)
Definition analyze (speculative : option bool) (print_name : option string)
    (machine_width : Target_system.Machine_width.t)
    (return_continuation exn_continuation : Continuation.t)
    (code_age_relation : Flambda2_types.Code_age_relation.t)
    (used_value_slots : Or_unknown.t Name_occurrences.t)
    (code_ids_to_never_delete : Code_id.Set_.t)
    (specialization_map : Continuation_callsite_map.t Continuation.t)
    (t : T.Acc.t) : M T.Flow_result.t :=
  (* 53: [?(speculative = false)] *)
  let& speculative :=
    match speculative with Some speculative => speculative | None => false end
  in
  Profile.record_call (Some true) "data_flow" (fun _ =>
    (* 57-61 *)
    (let! tmp1 := Flambda_features.dump_flow tt in
     if tmp1
     then
       (* PORT-GAP(papp): [Continuation_callsite_map.print] is given its
          first argument only. *)
       let! tmp2 := papp1 Continuation_callsite_map.print Continuation.print in
       Format.eprintf4 "PRESOURCE:@
spec:%a@
%a@
@." tmp2 specialization_map T.Acc.print t
     else ret tt) ;;
    (* Accumulator normalization *)
    (* 63-70: [({ T.Acc.stack; map; ...; dummy_toplevel_cont } as t)] *)
    let* t := Flow_acc.normalize_acc specialization_map t in
    let* '{| T.Acc.stack := stack;
             T.Acc.map := map;
             T.Acc.extra := _;
             T.Acc.lifted_constants := _;
             T.Acc.dummy_toplevel_cont := dummy_toplevel_cont
          |} :=
      ret t
    in
    (* 71 *)
    assert_ (match stack with [] => true | _ :: _ => false end) ;;
    (* 72-76 *)
    (let! tmp1 := Continuation.name dummy_toplevel_cont in
     let! tmp2 := String.equal tmp1 Flow_acc.wrong_dummy_toplevel_cont_name in
     assert_ (negb tmp2)) ;;
    (* 77-78 *)
    (let! tmp1 := Flambda_features.dump_flow tt in
     if tmp1
     then Format.eprintf2 "SOURCE:@
%a@
@." T.Acc.print t
     else ret tt) ;;
    (* dependency graph *)
    (* 80-83: the arguments are in the order of the interface. *)
    let* deps :=
      Data_flow_graph.create return_continuation exn_continuation
        code_age_relation used_value_slots code_ids_to_never_delete map
    in
    (* 84-85 *)
    (let! tmp1 := Flambda_features.dump_flow tt in
     if tmp1
     then Format.eprintf2 "/// graph@
%a@
@." Data_flow_graph.print deps
     else ret tt) ;;
    (* Dead variable analysis *)
    let* dead_variable_result := Data_flow_graph.required_names deps in
    (* Aliases analysis *)
    (* 89-92 *)
    let* dom_graph :=
      Dominator_graph.create
        dead_variable_result.(Flow_types.Data_flow_result.required_names)
        return_continuation exn_continuation map
    in
    let* aliases := Dominator_graph.dominator_analysis dom_graph in
    let* aliases_kind := Dominator_graph.aliases_kind dom_graph aliases in
    (* 95-98: [~print:(Dominator_graph.Dot.print ~doms:aliases)] is the
       function of the arguments that are left. *)
    (let! tmp1 := Flambda_features.dump_flow tt in
     if tmp1
     then
       print_graph
         (fun ctx print_name ppf graph =>
           Dominator_graph.Dot.print ctx print_name aliases ppf graph)
         print_name dominator_graph_ppf dom_graph
     else ret tt) ;;
    (* control flow graph *)
    let* control := Control_flow_graph.create dummy_toplevel_cont t in
    (* 101-106 *)
    let* reference_analysis :=
      Mutable_unboxing.create aliases dom_graph t control
        dead_variable_result.(Flow_types.Data_flow_result.required_names)
        return_continuation exn_continuation machine_width
    in
    (* PORT-GAP(papp): 107, [Mutable_unboxing.pp_node] is given its first
       argument only. *)
    let* pp_node := papp1 Mutable_unboxing.pp_node reference_analysis in
    let* '(reference_result, unboxed_blocks) :=
      Mutable_unboxing.make_result reference_analysis
    in
    (* 111-115 *)
    let* continuation_parameters :=
      Control_flow_graph.compute_continuation_extra_args_for_aliases
        speculative
        dead_variable_result.(Flow_types.Data_flow_result.required_names)
        t unboxed_blocks aliases control
    in
    (* 116-121: [~print:(Control_flow_graph.Dot.print ~df:t ...)] is the
       function of the arguments that are left. *)
    (let! tmp1 := Flambda_features.dump_flow tt in
     if tmp1
     then
       print_graph
         (fun ctx print_name ppf graph =>
           Control_flow_graph.Dot.print ctx t print_name ppf
             return_continuation exn_continuation (Some pp_node)
             continuation_parameters graph)
         print_name control_flow_graph_ppf control
     else ret tt) ;;
    (* 122-135 *)
    let* required_names_after_ref_reference_analysis :=
      (* CR pchambart/gbury: this is an overapproximation of actually used new
         parameters. We might want to filter this using another round of
         dead_analysis *)
      Continuation.Map.fold
        (fun _cont epa required_names =>
          let* params :=
            let! tmp1 :=
              Continuation_extra_params_and_args.extra_params epa
            in
            Bound_parameters.var_set tmp1
          in
          let! tmp1 := Name.set_of_var_set params in
          Name.Set_.union required_names tmp1)
        reference_result.(Flow_types.Mutable_unboxing_result.additional_epa)
        dead_variable_result.(Flow_types.Data_flow_result.required_names)
    in
    (* 136-145 *)
    let& result :=
      {| T.Flow_result.data_flow_result :=
           {| T.Data_flow_result.required_names :=
                required_names_after_ref_reference_analysis;
              T.Data_flow_result.reachable_code_ids :=
                dead_variable_result.(Flow_types.Data_flow_result.reachable_code_ids)
           |};
         T.Flow_result.aliases_result :=
           {| T.Alias_result.aliases_kind := aliases_kind;
              T.Alias_result.continuation_parameters :=
                continuation_parameters
           |};
         T.Flow_result.mutable_unboxing_result := reference_result
      |}
    in
    (* 146-147 *)
    (let! tmp1 := Flambda_features.dump_flow tt in
     if tmp1
     then Format.eprintf2 "/// result@
%a@
@." T.Flow_result.print result
     else ret tt) ;;
    (* return *)
    ret result).

(* PORT-GAP(verbatim): 53-55, the compiler's function with its optional
   arguments. *)
(*OCAML-END
let analyze ?speculative ?print_name machine_width return_continuation
    exn_continuation code_age_relation used_value_slots
    code_ids_to_never_delete specialization_map t =
  analyze speculative print_name machine_width return_continuation
    exn_continuation code_age_relation used_value_slots
    code_ids_to_never_delete specialization_map t
OCAML-END*)

(* 151-182 *)
Definition did_perform_mutable_unboxing (result : T.Flow_result.t) : M bool :=
  (* This function is used to determine whether the mutable unboxing pass
     generated code that warrants running a second pass of Simplify on a
     function's code.

     The mutable unboxing pass can actually also unbox immutable things. This is
     useful because it can unbox some more things than the regular unboxing pass
     (for instance, blocks in loops where the kind is not precise enough).
     However, in some cases, the mutable unboxing pass will only do the same
     unboxing as the regular continuation parameter unboxing, and in such cases,
     we would like not to trigger a second pass of Simplify[1]. However,
     whenever a mutable block is unboxed, even when the unboxing is trivial, it
     creates new opportunities for the downwards pass to propagate more
     information (because currently the typing env does not track anything about
     the contents of mutable blocks). Therefore, it might be beneficial to do
     another round of simplifications if we did unbox at least one mutable
     block.

     [1]: In such cases the continuation param unboxing will have already
     rewritten most uses, so the mutable unboxing will only emit [Remove_prim]
     rewrites. Such rewrites are actually superfluous because the upwards pass
     of Simplify would already remove these bindings. Therefore, when all the
     rewrites generated by the mutable unboxing pass are [Remove_prim] rewrites,
     we can consider that the mutable unboxing pass did not actually make any
     useful change, and thus we do not need to redo a pass of Simplify. *)
  or_else
    result.(Flow_types.Flow_result.mutable_unboxing_result).(Flow_types.Mutable_unboxing_result.did_unbox_a_mutable_block)
    (Named_rewrite_id.Map.exists_
       (fun _ named_rewrite =>
         match named_rewrite with
         | Named_rewrite.Prim_rewrite Named_rewrite.Prim_rewrite.Remove_prim =>
           ret false
         | Named_rewrite.Prim_rewrite (Named_rewrite.Prim_rewrite.Invalid _)
         | Named_rewrite.Prim_rewrite
             (Named_rewrite.Prim_rewrite.Replace_by_binding _ _) =>
           ret true
         end)
       result.(Flow_types.Flow_result.mutable_unboxing_result).(Flow_types.Mutable_unboxing_result.let_rewrites)).

(* 184-211 *)
Definition added_useful_alias_in_loop
    (typing_env : Flambda2_types.Typing_env.t) (acc : T.Acc.t)
    (result : T.Flow_result.t) : M bool :=
  Seq.exists2_
    (* 187-188: the two arguments are pairs, which the compiler's function
       takes apart in its parameters. *)
    (fun pat pat' =>
      let* '(k, continuation_info) := ret pat in
      let* '(k', continuation_param_aliases) := ret pat' in
      (let! tmp1 := Continuation.equal k k' in
       if negb tmp1
       then
         fatal_errorf0
           "[Flow Analysis]: Mismatch beetween continuation maps for source info and continuation params alias result"
       else ret tt) ;;
      and_then continuation_info.(Flow_types.Continuation_info.recursive)
        (Variable_.Lmap.exists_
           (fun _var bound_to =>
             (* 197-208: the arguments are in the order of the interface:
                [~var ~symbol ~const]. *)
             Simple.pattern_match' bound_to
               (fun _ _ =>
                 (* variables may not be bound in the typing env at this
                    point *)
                 ret false)
               (fun sym _ =>
                 let* ty :=
                   let! tmp1 := Name.symbol sym in
                   Flambda2_types.Typing_env.find typing_env tmp1
                     (Some Flambda_kind.value)
                 in
                 let! tmp1 := Flambda2_types.is_unknown typing_env ty in
                 ret (negb tmp1))
               (fun _ => ret true))
           continuation_param_aliases.(Flow_types.Continuation_param_aliases.lets_to_introduce)))
    (Continuation.Map.to_seq acc.(Flow_types.Acc.map))
    (Continuation.Map.to_seq
       result.(Flow_types.Flow_result.aliases_result).(Flow_types.Alias_result.continuation_parameters)).
