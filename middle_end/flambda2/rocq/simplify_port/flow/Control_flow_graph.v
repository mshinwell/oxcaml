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

(* This file follows middle_end/flambda2/simplify/flow/control_flow_graph.ml
   at commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive function)
   is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Array Bound_parameter Bound_parameters
  Continuation Continuation_extra_params_and_args Dominator_graph
  Flambda_colours Flow_types Format List Name Option Or_null Queue Simple
  Stdlib_ String Variable_.
From SimplifyPort.decl Require Import Control_flow_graph__local.
(* CONSTRUCTORS-WITHOUT-MODULE: Or_null.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
From SimplifyPort.abbrev.control_flow_graph Require Import Port_abbreviations.
(*OCAML
module T = Flow_types
OCAML*)

(* 16. The module that the file makes with a functor;
   decl/Control_flow_graph__local.v declares what the file uses of it. *)
(*OCAML
module G = Strongly_connected_components.Make (Continuation)
OCAML*)

(* 18-23 *)
Record t : Type :=
  { dummy_toplevel_cont : Continuation.t;
    callers : G.directed_graph;
    parents : Continuation.Map.t Continuation.t;
    children : Continuation.Map.t Continuation.Set_.t
  }.

(* 25-32. A variant with an inline record: in Rocq the two fields of [Aliased]
   are by place; the extracted file has the compiler's definition, which the
   directive of [exn_param_alias] holds. *)
Inductive exn_param_alias_ : Type :=
  | Not_aliased
  | Aliased_to_poison
  | Aliased_to_a_symbol
  | Aliased (alias_var : Variable_.t) (exception_param : Variable_.t).
Extract Inductive exn_param_alias_ => "exn_param_alias"
  [ "Not_aliased" "Aliased_to_poison" "Aliased_to_a_symbol"
    "(fun (x__1, x__2) -> Aliased { alias_var = x__1; exception_param = x__2 })" ]
  "(fun f__1 f__2 f__3 f__4 x__0 -> match x__0 with Not_aliased -> f__1 () | Aliased_to_poison -> f__2 () | Aliased_to_a_symbol -> f__3 () | Aliased { alias_var = x__1; exception_param = x__2 } -> f__4 x__1 x__2)".
Definition exn_param_alias : Type := exn_param_alias_.
Extract Constant exn_param_alias => "
  | Not_aliased
  | Aliased_to_poison
  | Aliased_to_a_symbol
  | Aliased of
      { alias_var : Variable.t;
        exception_param : Variable.t
      }".

(* 34-74. The compiler's second parameter is the pattern
   [{ T.Acc.map; _ }]. *)
Definition create (dummy_toplevel_cont : Continuation.t)
    (source_info : T.Acc.t) : M Control_flow_graph.t :=
  let* '{| T.Acc.map := map |} := ret source_info in
  let* parents :=
    Continuation.Map.filter_map
      (fun _ elt =>
        ret elt.(Flow_types.Continuation_info.parent_continuation))
      map
  in
  let* children :=
    Continuation.Map.fold
      (fun k parent acc =>
        Continuation.Map.update parent
          (fun x =>
            match x with
            | None =>
              let! tmp1 := Continuation.Set_.singleton k in
              ret (Some tmp1)
            | Some set =>
              let! tmp1 := Continuation.Set_.add k set in
              ret (Some tmp1)
            end)
          acc)
      parents Continuation.Map.empty
  in
  let* callers :=
    let! tmp1 :=
      Continuation.Map.singleton dummy_toplevel_cont Continuation.Set_.empty
    in
    Continuation.Map.fold
      (fun caller elt acc =>
        let* acc :=
          (* ensure that continuations that are never called, have a mapping in
             the graph (this is a requirement of the strongly connected
             component algorithm). *)
          Continuation.Map.update caller
            (fun res =>
              match res with
              | None => ret (Some Continuation.Set_.empty)
              | Some _ => ret res
              end)
            acc
        in
        let* acc :=
          Continuation.Map.update_many
            (fun _callee acc_opt _args =>
              match acc_opt with
              | None =>
                let! tmp2 := Continuation.Set_.singleton caller in
                ret (Some tmp2)
              | Some set =>
                let! tmp2 := Continuation.Set_.add caller set in
                ret (Some tmp2)
              end)
            acc elt.(Flow_types.Continuation_info.apply_cont_args)
        in
        ret acc)
      map tmp1
  in
  ret
    {| Control_flow_graph.dummy_toplevel_cont := dummy_toplevel_cont;
       Control_flow_graph.callers := callers;
       Control_flow_graph.parents := parents;
       Control_flow_graph.children := children
    |}.

(* This does not need to be tail-rec as other parts of flambda2 are already not
   tail-rec in the number of nested continuations. *)
(* 78-89. The compiler's first parameter is the pattern
   [{ children; dummy_toplevel_cont; _ }]. *)
Definition map_fold_on_children {Acc A : Type} (t : Control_flow_graph.t)
    (f : Continuation.t -> Acc -> M (Acc * A)) (acc : Acc)
    : M (Continuation.Map.t A) :=
  let* '{| Control_flow_graph.children := children;
           Control_flow_graph.dummy_toplevel_cont := dummy_toplevel_cont
        |} :=
    ret t
  in
  (* 79: a local [let rec] is Rocq's own [let] of a [fix]. *)
  let aux :=
    fix aux (fuel : Port_monad.fuel) (k : Continuation.t) (acc : Acc)
        {struct fuel} : M (Continuation.Map.t A) :=
      recursive! fuel in
      let* '(acc, to_add) := f k acc in
      let* map := Continuation.Map.singleton k to_add in
      let! tmp1 := Continuation.Map.find_or_null k children in
      match tmp1 with
      | Or_null.Null => ret map
      | Or_null.This s =>
        Continuation.Set_.fold
          (fun child map =>
            let! tmp2 := aux fuel child acc in
            Continuation.Map.disjoint_union None None map tmp2)
          s map
      end
  in
  let_fuel! fuel in
  aux fuel dummy_toplevel_cont acc.

(* 91-108 *)
Definition compute_available_variables (source_info : T.Acc.t)
    (t : Control_flow_graph.t) : M (Continuation.Map.t Variable_.Set_.t) :=
  map_fold_on_children t
    (fun k acc =>
      let* elt := Continuation.Map.find k source_info.(Flow_types.Acc.map) in
      let* extra_vars :=
        let! tmp1 :=
          Continuation.Map.find_or_null k source_info.(Flow_types.Acc.extra)
        in
        match tmp1 with
        | Or_null.Null => ret Variable_.Set_.empty
        | Or_null.This epa =>
          let! tmp2 := Continuation_extra_params_and_args.extra_params epa in
          Bound_parameters.var_set tmp2
        end
      in
      let* acc :=
        let! tmp1 :=
          Bound_parameters.var_set elt.(Flow_types.Continuation_info.params)
        in
        let! tmp2 := Variable_.Set_.union acc tmp1 in
        Variable_.Set_.union tmp2 extra_vars
      in
      ret (acc, acc))
    Variable_.Set_.empty.

(* 110-115 *)
Definition compute_added_extra_args
    (added_extra_args : Continuation.Map.t Variable_.Set_.t)
    (t : Control_flow_graph.t) : M (Continuation.Map.t Variable_.Set_.t) :=
  map_fold_on_children t
    (fun k available =>
      let! tmp1 := Continuation.Map.find k added_extra_args in
      let! tmp2 := Variable_.Set_.union tmp1 available in
      ret (tmp2, available))
    Variable_.Set_.empty.

(* 117-176 *)
Definition fixpoint {A : Type} (t : Control_flow_graph.t)
    (init : Continuation.Map.t A) (eq : A -> A -> M bool)
    (f : Continuation.t -> A -> Continuation.t -> A -> M A)
    : M (Continuation.Map.t A) :=
  let* components :=
    G.connected_components_sorted_from_roots_to_leaf
      t.(Control_flow_graph.callers)
  in
  let* res :=
    Array.fold_left
      (fun res component =>
        match component with
        | G.No_loop callee =>
          let! tmp1 := Continuation.Map.find_or_null callee res in
          match tmp1 with
          | Or_null.Null => ret res
          | Or_null.This callee_set =>
            let! tmp2 :=
              Continuation.Map.find callee t.(Control_flow_graph.callers)
            in
            Continuation.Set_.fold
              (fun caller res =>
                let* caller_set := Continuation.Map.find caller res in
                let* caller_new_set := f caller caller_set callee callee_set in
                Continuation.Map.add caller caller_new_set res)
              tmp2 res
          end
        | G.Has_loop conts =>
          let* q := Queue.create tt in
          List.iter (fun k => Queue.add k q) conts ;;
          (* We enforce the invariant that [q] contains no duplicates, and that
             [!q_s] precisely contains the continuations in [conts] that are not
             in [q]. Besides ensuring we don't add the same element twice to
             [q], this enforces as well that only continuations in the current
             strongly-connected component, that is, the continuations in
             [conts], can ever be in [q]. *)
          let* q_s := mk_ref Continuation.Set_.empty in
          let* cur := mk_ref res in
          while_
            (fun _ =>
              let! tmp1 := Queue.is_empty q in
              ret (negb tmp1))
            (fun _ =>
              let* callee := Queue.pop q in
              (let! tmp1 := get q_s in
               let! tmp2 := Continuation.Set_.add callee tmp1 in
               set q_s tmp2) ;;
              let* callee_set :=
                let! tmp1 := get cur in
                Continuation.Map.find callee tmp1
              in
              let* callers :=
                match_exn
                  (fun _ =>
                    Continuation.Map.find callee
                      t.(Control_flow_graph.callers))
                  Not_found
                  (fun _ =>
                    fatal_errorf2 "Callers not found for: %a"
                      Continuation.print callee)
                  (fun callers => ret callers)
              in
              Continuation.Set_.iter
                (fun caller =>
                  let* caller_set :=
                    let! tmp1 := get cur in
                    Continuation.Map.find caller tmp1
                  in
                  let* caller_new_set :=
                    f caller caller_set callee callee_set
                  in
                  let! tmp1 := eq caller_set caller_new_set in
                  if negb tmp1
                  then (
                    (let! tmp2 := get cur in
                     let! tmp3 :=
                       Continuation.Map.add caller caller_new_set tmp2
                     in
                     set cur tmp3) ;;
                    let! tmp2 := get q_s in
                    let! tmp3 := Continuation.Set_.mem caller tmp2 in
                    if tmp3
                    then (
                      Queue.add caller q ;;
                      let! tmp4 := get q_s in
                      let! tmp5 := Continuation.Set_.remove caller tmp4 in
                      set q_s tmp5)
                    else ret tt)
                  else ret tt)
                callers) ;;
          get cur
        end)
      init components
  in
  ret res.

(* 178-237 *)
Definition extra_args_for_aliases_overapproximation
    (required_names : Name.Set_.t) (source_info : T.Acc.t)
    (unboxed_blocks : Simple.Set_.t) (doms : Dominator_graph.alias_map)
    (t : Control_flow_graph.t) : M (Continuation.Map.t Variable_.Set_.t) :=
  let* available_variables := compute_available_variables source_info t in
  let& remove_vars_in_scope_of :=
    fun (k : Continuation.t) (var_set : Variable_.Set_.t) =>
    let* elt := Continuation.Map.find k source_info.(Flow_types.Acc.map) in
    let* res :=
      let! tmp1 := Continuation.Map.find k available_variables in
      Variable_.Set_.diff var_set tmp1
    in
    Variable_.Set_.diff res elt.(Flow_types.Continuation_info.defined)
  in
  (* We remove aliases to unboxed blocks, so that they won't try to be passed as
     extra args. These would normally be deleted, except in recursive
     continuations, where they would still be added and cause the code to
     fail. *)
  let* init :=
    Continuation.Map.mapi
      (fun k elt =>
        let* s :=
          let! tmp1 :=
            Bound_parameters.vars elt.(Flow_types.Continuation_info.params)
          in
          List.fold_left
            (fun acc param =>
              let! tmp2 := Variable_.Map.find_or_null param doms in
              match tmp2 with
              | Or_null.Null =>
                let! tmp3 := Name.var param in
                let! tmp4 := Name.Set_.mem tmp3 required_names in
                if tmp4
                then
                  fatal_errorf2 "Dom not found for: %a@." Variable_.print
                    param
                else ret acc
              | Or_null.This dom =>
                (* Parameters whose dominator/canonical alias is a symbol or a
                   constant do not require extra args to access the value of
                   that dominator. *)
                Simple.pattern_match' dom
                  (fun dom_var _ =>
                    let! tmp3 := Variable_.equal param dom_var in
                    let! tmp4 :=
                      or_else tmp3 (Simple.Set_.mem dom unboxed_blocks)
                    in
                    if tmp4 then ret acc else Variable_.Set_.add dom_var acc)
                  (fun _ _ => ret acc)
                  (fun _ => ret acc)
              end)
            Variable_.Set_.empty tmp1
        in
        let* s := remove_vars_in_scope_of k s in
        ret s)
      source_info.(Flow_types.Acc.map)
  in
  let* added_extra_args :=
    fixpoint t init Variable_.Set_.equal
      (fun caller caller_aliases_needed _ callee_aliases_needed =>
        let! tmp1 := remove_vars_in_scope_of caller callee_aliases_needed in
        Variable_.Set_.union caller_aliases_needed tmp1)
  in
  ret added_extra_args.

(* 239-337 *)
Definition minimize_extra_args_for_one_continuation (source_info : T.Acc.t)
    (unboxed_blocks : Simple.Set_.t)
    (available_added_extra_args : Continuation.Map.t Variable_.Set_.t)
    (doms : Variable_.Map.t Simple.t) (k : Continuation.t)
    (aliases_needed : Variable_.Set_.t) : M T.Continuation_param_aliases.t :=
  let* available := Continuation.Map.find k available_added_extra_args in
  let* extra_args_for_aliases := Variable_.Set_.diff aliases_needed available in
  let* elt := Continuation.Map.find k source_info.(Flow_types.Acc.map) in
  (* 244-254 *)
  let* exception_handler_first_param :=
    if elt.(Flow_types.Continuation_info.is_exn_handler)
    then
      let! tmp1 :=
        Bound_parameters.to_list elt.(Flow_types.Continuation_info.params)
      in
      match tmp1 with
      | [] =>
        fatal_errorf2
          "exception handler continuation %a must have at least one parameter"
          Continuation.print k
      | first :: _ =>
        let! tmp2 := Bound_parameter.var first in
        ret (Some tmp2)
      end
    else ret None
  in
  (* For exception continuations the first parameter cannot be removed, so
     instead of rewriting the parameter to its dominator, we instead rewrite
     every alias to the exception parameter *)
  (* 258-280 *)
  let* '(extra_args_for_aliases, exception_handler_first_param_aliased) :=
    match exception_handler_first_param with
    | None => ret (extra_args_for_aliases, Not_aliased)
    | Some exception_param =>
      let! tmp1 := Variable_.Map.find_or_null exception_param doms in
      match tmp1 with
      | Or_null.Null => ret (extra_args_for_aliases, Not_aliased)
      | Or_null.This alias =>
        Simple.pattern_match' alias
          (fun alias_var _ =>
            let! tmp2 := Variable_.equal exception_param alias_var in
            if tmp2
            then ret (extra_args_for_aliases, Not_aliased)
            else
              let! tmp3 :=
                Variable_.Set_.remove alias_var extra_args_for_aliases
              in
              ret (tmp3, Aliased alias_var exception_param))
          (fun _ _ => ret (extra_args_for_aliases, Aliased_to_a_symbol))
          (fun _ =>
            (* This can happen when the reaper is enabled and an exn parameter
               is unused. *)
            (* CR gbury/ncourant : when we have a proper poison constant, we
               could/should check that this is exactly the constant aliased *)
            ret (extra_args_for_aliases, Aliased_to_poison))
      end
    end
  in
  (* 281-287 *)
  let* lets_to_introduce :=
    match exception_handler_first_param_aliased with
    | Not_aliased | Aliased_to_a_symbol | Aliased_to_poison =>
      ret Variable_.Lmap.empty
    | Aliased alias exception_param =>
      let! tmp1 := Simple.var exception_param in
      Variable_.Lmap.singleton alias tmp1
    end
  in
  (* 288-323: the first argument of the function is the pair
     [(removed, lets_to_introduce)]. *)
  let* '(removed_aliased_params_and_extra_params, lets_to_introduce) :=
    let! tmp1 :=
      Bound_parameters.vars elt.(Flow_types.Continuation_info.params)
    in
    List.fold_left
      (fun pat param =>
        let* '(removed, lets_to_introduce) := ret pat in
        let& default :=
          fun (alias : Simple.t) =>
          let* removed := Variable_.Set_.add param removed in
          let* lets_to_introduce :=
            let! tmp2 := Simple.Set_.mem alias unboxed_blocks in
            if tmp2
            then ret lets_to_introduce
            else Variable_.Lmap.add param alias lets_to_introduce
          in
          ret (removed, lets_to_introduce)
        in
        let! tmp2 := Variable_.Map.find_or_null param doms in
        match tmp2 with
        | Or_null.Null => ret (removed, lets_to_introduce)
        | Or_null.This alias =>
          let! tmp3 := Simple.var param in
          let! tmp4 := Simple.equal tmp3 alias in
          if tmp4
          then ret (removed, lets_to_introduce)
          else
            match exception_handler_first_param_aliased with
            | Not_aliased => default alias
            | Aliased_to_a_symbol | Aliased_to_poison =>
              (* We cannot remove the exn param, so even if it is aliased to a
                 symbol, we cannot make use of that information. *)
              ret (removed, lets_to_introduce)
            | Aliased aliased_to exception_param =>
              let* is_first_exception_param :=
                Variable_.equal exception_param param
              in
              if is_first_exception_param
              then ret (removed, lets_to_introduce)
              else
                let! tmp5 := Simple.var aliased_to in
                let! tmp6 := Simple.equal alias tmp5 in
                if tmp6
                then
                  let! tmp7 := Simple.var exception_param in
                  default tmp7
                else default alias
            end
        end)
      (Variable_.Set_.empty, lets_to_introduce)
      tmp1
  in
  (* 324-329 *)
  let* recursive_continuation_wrapper :=
    let! tmp1 :=
      and_then elt.(Flow_types.Continuation_info.recursive)
        (let! tmp2 := Variable_.Set_.is_empty extra_args_for_aliases in
         ret (negb tmp2))
    in
    if tmp1
    then ret T.Continuation_param_aliases.Wrapper_needed
    else ret T.Continuation_param_aliases.No_wrapper
  in
  (* 330-337 *)
  let& res :=
    {| T.Continuation_param_aliases.extra_args_for_aliases :=
         extra_args_for_aliases;
       T.Continuation_param_aliases.removed_aliased_params_and_extra_params :=
         removed_aliased_params_and_extra_params;
       T.Continuation_param_aliases.lets_to_introduce := lets_to_introduce;
       T.Continuation_param_aliases.recursive_continuation_wrapper :=
         recursive_continuation_wrapper
    |}
  in
  ret res.

(* 339-347 *)
Definition minimize_extra_args_for_aliases (source_info : T.Acc.t)
    (unboxed_blocks : Simple.Set_.t) (doms : Variable_.Map.t Simple.t)
    (added_extra_args : Continuation.Map.t Variable_.Set_.t)
    (t : Control_flow_graph.t)
    : M (Continuation.Map.t T.Continuation_param_aliases.t) :=
  let* available_added_extra_args :=
    compute_added_extra_args added_extra_args t
  in
  Continuation.Map.mapi
    (minimize_extra_args_for_one_continuation source_info unboxed_blocks
       available_added_extra_args doms)
    added_extra_args.

(* 349-381 *)
Definition compute_continuation_extra_args_for_aliases (speculative : bool)
    (required_names : Name.Set_.t) (source_info : T.Acc.t)
    (unboxed_blocks : Simple.Set_.t) (doms : Variable_.Map.t Simple.t)
    (t : Control_flow_graph.t)
    : M (Continuation.Map.t T.Continuation_param_aliases.t) :=
  let* added_extra_args :=
    extra_args_for_aliases_overapproximation required_names source_info
      unboxed_blocks doms t
  in
  let* extra_args_for_toplevel_cont :=
    Continuation.Map.find t.(Control_flow_graph.dummy_toplevel_cont)
      added_extra_args
  in
  (* When doing speculative inlining, the flow analysis only has access to the
     inlined body of the function being (speculatively) inlined. Thus, it is
     possible for a canonical alias to be defined outside the inlined body (a
     typical occurrence would be a String length computed before the call of the
     inlined funciton, but shared with the uses inside the funciton by the cse).

     Note that while this is true for aliases, we do not need a similar
     mechanism for mutable unboxing, since when doing mutable unboxing, we
     require that we have seen the creation of the block. *)
  (let! tmp1 :=
     and_then (negb speculative)
       (let! tmp2 := Variable_.Set_.is_empty extra_args_for_toplevel_cont in
        ret (negb tmp2))
   in
   if tmp1
   then
     fatal_errorf2
       "ERROR:@
Toplevel continuation cannot have needed extra argument for aliases: %a@."
       Variable_.Set_.print extra_args_for_toplevel_cont
   else ret tt) ;;
  let* extra_args_for_aliases :=
    minimize_extra_args_for_aliases source_info unboxed_blocks doms
      added_extra_args t
  in
  ret extra_args_for_aliases.

(* 406 and 409. A function on characters, the argument of [String.map]: the
   kit has no character; the compiler's text. *)
Parameter braces_to_brackets : Stdlib_.char -> M Stdlib_.char.
Extract Inlined Constant braces_to_brackets =>
  "(function '{' -> '[' | '}' -> ']' | c -> c)".

(* 383-476 *)
Module Dot.
  (* 384-385 *)
  Definition node_id (ctx : int) (ppf : Format.formatter)
      (cont : Continuation.t) : M unit :=
    Format.fprintf2 ppf "node_%d_%d" ctx (Continuation.coerce_t_to_int cont).

  (* 387-411. [?(extra_args = Variable.Set.empty)] and [?(info = "")] are
     optional arguments in the compiler: by place here. *)
  Definition node (extra_args : option Variable_.Set_.t)
      (info : option string) (df : T.Acc.t)
      (pp_node : Format.formatter -> Continuation.t -> M unit) (ctx : int)
      (_ : unit) (ppf : Format.formatter) (cont : Continuation.t) : M unit :=
    let& extra_args :=
      match extra_args with
      | Some extra_args => extra_args
      | None => Variable_.Set_.empty
      end
    in
    let& info := match info with Some info => info | None => "" end in
    let* '(params, shape) :=
      let! tmp1 := Continuation.Map.find_or_null cont df.(Flow_types.Acc.map) in
      match tmp1 with
      | Or_null.Null => ret ("[ none ]", "")
      | Or_null.This elt =>
        let* params :=
          let! tmp2 :=
            Bound_parameters.vars elt.(Flow_types.Continuation_info.params)
          in
          let! tmp3 :=
            papp2 Format.pp_print_list
              (Some (fun ppf (_ : unit) => Format.fprintf0 ppf ", "))
              Variable_.print
          in
          Format.asprintf2 "[%a]" tmp3 tmp2
        in
        let& shape :=
          if elt.(Flow_types.Continuation_info.recursive)
          then "shape=record"
          else ""
        in
        ret (params, shape)
      end
    in
    let! tmp1 := Format.asprintf2 "%a" pp_node cont in
    let! tmp2 := String.map braces_to_brackets tmp1 in
    let! tmp3 := Format.asprintf2 "%a" Variable_.Set_.print extra_args in
    let! tmp4 := String.map braces_to_brackets tmp3 in
    Format.fprintf9 ppf "%a [label=""%a %s %s%s"" %s %s];@
" (node_id ctx) cont Continuation.print cont params tmp4 tmp2 shape info.

  (* 413-432 *)
  Definition nodes (df : T.Acc.t) (ctx : int)
      (return_continuation exn_continuation : Continuation.t)
      (continuation_parameters :
        Continuation.Map.t T.Continuation_param_aliases.t)
      (pp_node : Format.formatter -> Continuation.t -> M unit)
      (ppf : Format.formatter) (cont_map : Continuation.Set_.t) : M unit :=
    Continuation.Set_.iter
      (fun cont =>
        let* extra_args :=
          let! tmp1 := Continuation.Map.find_opt cont continuation_parameters in
          Option.map
            (fun continuation_parameters =>
              ret
                continuation_parameters.(Flow_types.Continuation_param_aliases.extra_args_for_aliases))
            tmp1
        in
        let* info :=
          let! tmp1 := Continuation.equal return_continuation cont in
          if tmp1
          then ret "color=blue"
          else
            let! tmp2 := Continuation.equal exn_continuation cont in
            if tmp2 then ret "color=red" else ret ""
        in
        node extra_args (Some info) df pp_node ctx tt ppf cont)
      cont_map.

  (* 434-436 *)
  Definition edge (ctx : int) (color : string) (ppf : Format.formatter)
      (src dst : Continuation.t) : M unit :=
    Format.fprintf5 ppf "%a -> %a [color=""%s""];@
" (node_id ctx) dst (node_id ctx) src color.

  (* 438-442 *)
  Definition edges (ctx : int) (color : string) (ppf : Format.formatter)
      (edge_map : Continuation.Map.t Continuation.Set_.t) : M unit :=
    Continuation.Map.iter
      (fun src dst_set =>
        Continuation.Set_.iter (fun dst => edge ctx color ppf src dst) dst_set)
      edge_map.

  (* 444-445 *)
  Definition edges' (ctx : int) (color : string) (ppf : Format.formatter)
      (edge_map : Continuation.Map.t Continuation.t) : M unit :=
    Continuation.Map.iter (fun src dst => edge ctx color ppf src dst) edge_map.

  (* 447-475. [?(pp_node = fun _ppf _cont -> ())] is an optional argument in
     the compiler: by place here; [print] below is the compiler's
     function. *)
  Definition print_ (ctx : int) (df : T.Acc.t) (print_name : string)
      (ppf : Format.formatter)
      (return_continuation exn_continuation : Continuation.t)
      (pp_node : option (Format.formatter -> Continuation.t -> M unit))
      (continuation_parameters :
        Continuation.Map.t T.Continuation_param_aliases.t)
      (t : Control_flow_graph.t) : M unit :=
    let& pp_node :=
      match pp_node with
      | Some pp_node => pp_node
      | None => fun _ppf _cont => ret tt
      end
    in
    let& dummy_toplevel_cont := t.(Control_flow_graph.dummy_toplevel_cont) in
    let* all_conts :=
      let! tmp1 :=
        Continuation.Set_.of_list
          [dummy_toplevel_cont; return_continuation; exn_continuation]
      in
      Continuation.Map.fold
        (fun cont callers acc =>
          let! tmp2 := Continuation.Set_.union callers acc in
          Continuation.Set_.add cont tmp2)
        t.(Control_flow_graph.callers)
        tmp1
    in
    let* all_conts :=
      Continuation.Map.fold
        (fun cont _parent acc => Continuation.Set_.add cont acc)
        t.(Control_flow_graph.parents) all_conts
    in
    Flambda_colours.without_colours (fun _ =>
      Format.fprintf10 ppf "subgraph cluster_%d { label=""%s"";@
%a%a@
%a@
%a@
}@." ctx print_name
        (node None None df pp_node ctx tt)
        dummy_toplevel_cont
        (nodes df ctx return_continuation exn_continuation
           continuation_parameters pp_node)
        all_conts
        (edges' ctx "green")
        t.(Control_flow_graph.parents)
        (edges ctx "black")
        t.(Control_flow_graph.callers)).

  (* PORT-GAP(verbatim): 447-448, the compiler's function with its optional
     argument [?pp_node]: the text of the directive, which Rocq prints at
     this place. *)
  Definition print := print_.
  Extract Constant print =>
    "fun ctx df print_name ppf return_continuation exn_continuation ?pp_node continuation_parameters t -> print_ ctx df print_name ppf return_continuation exn_continuation pp_node continuation_parameters t".
End Dot.
