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
   middle_end/flambda2/rocq/simplify_port/flow/Dominator_graph.v, which follows
   middle_end/flambda2/simplify/flow/dominator_graph.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module T = Flow_types
module G = Strongly_connected_components.Make (Simple)
open Port_abbreviations
open Port_monad

type t =
  { required_names : Name.Set.t;
    params_kind : Flambda_kind.With_subkind.t Variable_.Map.t;
    graph : G.directed_graph;
    dominator_roots : Simple.Set.t
  }

(** val required_names : t -> Name.Set.t **)

let required_names t0 = t0.required_names

(** val params_kind : t -> Flambda_kind.With_subkind.t Variable_.Map.t **)

let params_kind t0 = t0.params_kind

(** val graph : t -> G.directed_graph **)

let graph t0 = t0.graph

(** val dominator_roots : t -> Simple.Set.t **)

let dominator_roots t0 = t0.dominator_roots

type alias_map = Simple.t Variable_.Map.t

(** val empty : Name.Set.t -> t coq_M **)

let empty required_names0 =
  let graph0 = Simple.Map.empty in
  let dominator_roots0 = Simple.Set.empty in
  let params_kind0 = Variable.Map.empty in
  { required_names = required_names0;
    params_kind = params_kind0;
    graph = graph0;
    dominator_roots = dominator_roots0
  }

(** val add_node_aux : t -> Simple.t -> t coq_M **)

let add_node_aux t0 simple =
  let graph0 =
    Simple.Map.update simple
      (fun res ->
        match res with Some _ -> res | None -> Some Simple.Set.empty)
      t0.graph
  in
  (fun t graph -> { t with graph }) t0 graph0

(** val add_node : t -> Simple.t -> t coq_M **)

let add_node t0 simple =
  Simple.pattern_match simple
    (fun name _ ->
      if Name.Set.mem name t0.required_names then add_node_aux t0 simple else t0)
    (fun _ -> add_node_aux t0 simple)

(** val add_root : Variable.t -> t -> t coq_M **)

let add_root var t0 =
  if not (Name.Set.mem (Name.var var) t0.required_names)
  then t0
  else
    (fun t dominator_roots -> { t with dominator_roots })
      t0
      (Simple.Set.add (Simple.var var) t0.dominator_roots)

(** val add_edge : Variable.t -> Simple.t -> t -> t coq_M **)

let add_edge src dst t0 =
  if not (Name.Set.mem (Name.var src) t0.required_names)
  then t0
  else
    let graph0 =
      Simple.Map.update (Simple.var src)
        (fun x ->
          match x with
          | Some s -> Some (Simple.Set.add dst s)
          | None -> Some (Simple.Set.singleton dst))
        t0.graph
    in
    (fun t graph -> { t with graph }) t0 graph0

(** val add_continuation_info : T.Continuation_info.t Continuation.Map.t ->
    Continuation.t -> T.Continuation_info.t -> t -> Continuation.t ->
    Continuation.t -> t coq_M **)

let add_continuation_info map _ elt t0 return_continuation exn_continuation =
  let t1 =
    List.fold_left
      (fun t1 bp ->
        let var = Bound_parameter.var bp in
        let t2 = add_node t1 (Simple.var var) in
        let params_kind0 =
          Variable.Map.add var (Bound_parameter.kind bp) t2.params_kind
        in
        (fun t params_kind -> { t with params_kind }) t2 params_kind0)
      t0
      (Bound_parameters.to_list elt.Flow_types.Continuation_info.params)
  in
  let t2 =
    Variable.Map.fold add_edge elt.Flow_types.Continuation_info.direct_aliases
      t1
  in
  Continuation.Map.fold
    (fun k rewrite_ids t3 ->
      if
        Continuation.equal return_continuation k
        || Continuation.equal exn_continuation k
      then t3
      else
        let params0 =
          Port_monad.match_exn
            (fun _ -> Continuation.Map.find k map)
            Port_monad.not_found
            (fun _ ->
              Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
                Continuation.print k)
            (fun elt0 ->
              Array.of_list
                (Bound_parameters.vars elt0.Flow_types.Continuation_info.params))
        in
        Apply_cont_rewrite_id.Map.fold
          (fun _ args t4 ->
            Numeric_types.Int.Map.fold
              (fun i dst t5 ->
                let src = Array.get params0 i in
                match dst with
                | T.Cont_arg.Function_result -> add_root src t5
                | T.Cont_arg.Simple dst0 -> add_edge src dst0 t5
                | T.Cont_arg.New_let_binding (var, _) ->
                  let t6 = add_root var t5 in
                  add_edge src (Simple.var var) t6)
              args t4)
          rewrite_ids t3)
    elt.Flow_types.Continuation_info.apply_cont_args t2

(** val create : Name.Set.t -> Continuation.t -> Continuation.t ->
    T.Continuation_info.t Continuation.Map.t -> t coq_M **)

let create required_names0 return_continuation exn_continuation map =
  let t0 = empty required_names0 in
  let t1 =
    Continuation.Map.fold
      (fun k elt t1 ->
        add_continuation_info map k elt t1 return_continuation exn_continuation)
      map t0
  in
  let all_simples =
    Simple.Map.fold
      (fun s dsts acc -> Simple.Set.add s (Simple.Set.union dsts acc))
      t1.graph t1.dominator_roots
  in
  let t2 =
    Simple.Set.fold
      (fun var t2 ->
        let graph0 =
          Simple.Map.update var
            (fun res ->
              match res with Some _ -> res | None -> Some Simple.Set.empty)
            t2.graph
        in
        (fun t graph -> { t with graph }) t2 graph0)
      all_simples t1
  in
  t2

(** val find_dom : Simple.t -> alias_map -> Simple.t coq_M **)

let find_dom simple doms =
  Simple.pattern_match' simple
    (fun var _ ->
      match Variable.Map.find_or_null var doms with
      | Null -> simple
      | This dom -> dom)
    (fun _ _ -> simple)
    (fun _ -> simple)

(** val update_doms_for_one_var : t -> alias_map -> Variable.t -> alias_map
    coq_M **)

let update_doms_for_one_var t0 doms var =
  let { required_names = _;
        params_kind = _;
        graph = graph0;
        dominator_roots = dominator_roots0
      } =
    t0
  in
  let simple = Simple.var var in
  let dom =
    if Simple.Set.mem simple dominator_roots0
    then simple
    else
      match Simple.Map.find_or_null simple graph0 with
      | Null -> simple
      | This predecessors -> (
        let s =
          Simple.Set.map
            (fun predecessor -> find_dom predecessor doms)
            predecessors
        in
        match Simple.Set.get_singleton s with
        | Some ret_ -> ret_
        | None -> simple)
  in
  Variable.Map.add var dom doms

(** val initialize_doms_for_fixpoint : t -> alias_map -> Simple.t list ->
    Simple.Set.t Simple.Map.t coq_M **)

let initialize_doms_for_fixpoint t0 doms simples =
  let { required_names = _;
        params_kind = _;
        graph = graph0;
        dominator_roots = _
      } =
    t0
  in
  let all_predecessors =
    List.fold_left
      (fun acc var ->
        let predecessors =
          Port_monad.try_with
            (fun _ -> Simple.Map.find var graph0)
            Port_monad.not_found
            (fun _ -> assert false)
        in
        Simple.Set.union predecessors acc)
      Simple.Set.empty simples
  in
  let init_doms =
    Simple.Set.map (fun simple -> find_dom simple doms) all_predecessors
  in
  let outside_cycle =
    Simple.Map.of_set
      (fun simple -> Simple.Set.singleton (find_dom simple doms))
      (Simple.Set.diff all_predecessors (Simple.Set.of_list simples))
  in
  List.fold_left
    (fun doms0 simple -> Simple.Map.add simple init_doms doms0)
    outside_cycle simples

(** val dom_fixpoint : t -> Simple.Set.t Simple.Map.t -> Simple.t list ->
    Simple.Set.t Simple.Map.t coq_M **)

let rec dom_fixpoint t0 acc simples =
  let { required_names = _;
        params_kind = _;
        graph = graph0;
        dominator_roots = dominator_roots0
      } =
    t0
  in
  let acc' =
    List.fold_left
      (fun acc0 simple ->
        if Simple.Set.mem simple dominator_roots0
        then Simple.Map.add simple (Simple.Set.singleton simple) acc0
        else
          let init_doms = Simple.Map.find simple acc0 in
          let predecessors =
            Port_monad.try_with
              (fun _ -> Simple.Map.find simple graph0)
              Port_monad.not_found
              (fun _ -> assert false)
          in
          let new_doms =
            Simple.Set.fold
              (fun predecessor new_doms ->
                Simple.Set.inter new_doms (Simple.Map.find predecessor acc0))
              predecessors init_doms
          in
          let new_doms0 = Simple.Set.add simple new_doms in
          Simple.Map.add simple new_doms0 acc0)
      acc simples
  in
  if Simple.Map.equal Simple.Set.equal acc acc'
  then acc
  else dom_fixpoint t0 acc' simples

(** val extract_doms : alias_map -> Simple.Set.t Simple.Map.t -> Simple.t list
    -> alias_map coq_M **)

let extract_doms doms fixpoint_result simples =
  let simple_set = Simple.Set.of_list simples in
  List.fold_left
    (fun doms0 simple ->
      let var =
        Simple.pattern_match' simple
          (fun v _ -> v)
          (fun _ _ ->
            Misc.fatal_errorf
              "Cycles in the dominator analysis should never contain symbols")
          (fun _ ->
            Misc.fatal_errorf
              "Cycles in the dominator analysis should never contain constants")
      in
      let fixpoint_doms = Simple.Map.find simple fixpoint_result in
      let var_doms = Simple.Set.diff fixpoint_doms simple_set in
      let cardinal = Simple.Set.cardinal var_doms in
      let () = assert (cardinal <= 1) in
      let dom = if cardinal = 1 then Simple.Set.choose var_doms else simple in
      Variable.Map.add var dom doms0)
    doms simples

(** val dominator_analysis : t -> alias_map coq_M **)

let dominator_analysis t0 =
  let { required_names = _;
        params_kind = _;
        graph = graph0;
        dominator_roots = _
      } =
    t0
  in
  let components = G.connected_components_sorted_from_roots_to_leaf graph0 in
  let dominators =
    Array.fold_right
      (fun component doms ->
        match component with
        | G.Has_loop simples ->
          let loop_doms = initialize_doms_for_fixpoint t0 doms simples in
          let loop_result = dom_fixpoint t0 loop_doms simples in
          let doms0 = extract_doms doms loop_result simples in
          doms0
        | G.No_loop simple ->
          Simple.pattern_match' simple
            (fun var _ -> update_doms_for_one_var t0 doms var)
            (fun _ _ -> doms)
            (fun _ -> doms))
      components Variable.Map.empty
  in
  dominators

(** val aliases_kind : t -> alias_map -> Flambda_kind.t Variable_.Map.t coq_M **)

let aliases_kind t0 aliases =
  let { required_names = required_names0;
        params_kind = params_kind0;
        graph = _;
        dominator_roots = _
      } =
    t0
  in
  Variable.Map.fold
    (fun param kind acc ->
      if not (Name.Set.mem (Name.var param) required_names0)
      then acc
      else
        let alias = Variable.Map.find param aliases in
        let kind0 = Flambda_kind.With_subkind.kind kind in
        Simple.pattern_match' alias
          (fun v _ ->
            let () =
              match Variable.Map.find_or_null v acc with
              | Null -> ()
              | This alias_kind ->
                if not (Flambda_kind.equal kind0 alias_kind)
                then Misc.fatal_errorf "Incoherent kinds for aliases !"
                else ()
            in
            Variable.Map.add v kind0 acc)
          (fun _ _ -> acc)
          (fun _ -> acc))
    params_kind0 Variable.Map.empty

module Dot = struct
  (** val node_id : int -> Format.formatter -> Simple.t -> unit coq_M **)

  let node_id ctx ppf simple =
    Format.fprintf ppf "node_%d_%d" ctx
      ((fun (x__1 : Simple.t) -> (x__1 :> int)) simple)

  (** val node : int -> bool -> Format.formatter -> Simple.t -> unit coq_M **)

  let node ctx root ppf simple =
    if root
    then
      Format.fprintf ppf "%a [shape=record label=\"%a\"];@\n" (node_id ctx)
        simple Simple.print simple
    else
      Format.fprintf ppf "%a [label=\"%a\"];@\n" (node_id ctx) simple
        Simple.print simple

  (** val nodes : int -> Simple.Set.t -> Format.formatter -> 'a1 Simple.Map.t ->
      unit coq_M **)

  let nodes ctx roots ppf map =
    Simple.Map.iter
      (fun simple _ ->
        let root =
          Simple.pattern_match' simple
            (fun _ _ -> Simple.Set.mem simple roots)
            (fun _ _ -> true)
            (fun _ -> true)
        in
        node ctx root ppf simple)
      map

  (** val edge : int -> string -> Format.formatter -> Simple.t -> Simple.t ->
      unit coq_M **)

  let edge ctx color ppf src dst =
    Format.fprintf ppf "%a -> %a [color=\"%s\"];@\n" (node_id ctx) src
      (node_id ctx) dst color

  (** val edges : int -> string -> Format.formatter -> Simple.Set.t Simple.Map.t
      -> unit coq_M **)

  let edges ctx color ppf edge_map =
    Simple.Map.iter
      (fun src dst_set ->
        Simple.Set.iter (fun dst -> edge ctx color ppf src dst) dst_set)
      edge_map

  (** val edges' : int -> string -> Format.formatter -> Simple.t Variable_.Map.t
      -> unit coq_M **)

  let edges' ctx color ppf edge_map =
    Variable.Map.iter
      (fun src dst -> edge ctx color ppf (Simple.var src) dst)
      edge_map

  (** val print : int -> string -> alias_map -> Format.formatter -> t -> unit
      coq_M **)

  let print ctx print_name doms ppf t0 =
    Flambda_colours.without_colours (fun _ ->
        Format.fprintf ppf
          "subgraph cluster_%d { label=\"%s\"@\n%a@\n%a@\n%a@\n}@." ctx
          print_name
          (nodes ctx t0.dominator_roots)
          t0.graph (edges ctx "black") t0.graph (edges' ctx "red") doms)
end
