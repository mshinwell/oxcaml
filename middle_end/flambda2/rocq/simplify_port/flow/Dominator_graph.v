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

(* This file follows middle_end/flambda2/simplify/flow/dominator_graph.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive function)
   is that of GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Import Dominator_graph__local.
From SimplifyPort.decl Require Apply_cont_rewrite_id Array Bound_parameter
  Bound_parameters Continuation Flambda_colours Flambda_kind Flow_types
  Format Name Numeric_types Or_null Simple Variable_.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
Module T := Flow_types.

(* PORT-GAP(verbatim): 16, the module that the file makes with a functor;
   decl/Dominator_graph__local.v declares what the file uses of it. *)
(*OCAML
module G = Strongly_connected_components.Make (Simple)
OCAML*)

(* PORT-GAP(decl): [List.fold_left]. In the extracted file Rocq writes
   [open Simple] (the file names the type [Simple.Map.t] with an argument),
   and the declarations of [Simple] have a module [List], which hides the
   standard library's: the realisation "List.fold_left" of decl/List.v
   would not be found. The same declaration, realised by its full name. *)
Module Stdlib_List.
  Parameter fold_left :
    forall {Acc A : Type}, (Acc -> A -> M Acc) -> Acc -> list A -> M Acc.
  Extract Inlined Constant fold_left => "Stdlib.List.fold_left".
End Stdlib_List.

(* 18-25 *)
Record t : Type :=
  { required_names : Name.Set_.t;
    params_kind : Variable_.Map.t Flambda_kind.With_subkind.t;
    graph : G.directed_graph;
    dominator_roots : Simple.Set_.t
        (* variables that are dominated only by themselves, such as variables
           that are let-bound in a continuation (and that are not aliases). *)
  }.

(* 27 *)
Definition alias_map : Type := Variable_.Map.t Simple.t.

(* 29-33 *)
Definition empty (required_names : Name.Set_.t) : M Dominator_graph.t :=
  let& graph := Simple.Map.empty in
  let& dominator_roots := Simple.Set_.empty in
  let& params_kind := Variable_.Map.empty in
  ret
    {| Dominator_graph.required_names := required_names;
       Dominator_graph.params_kind := params_kind;
       Dominator_graph.graph := graph;
       Dominator_graph.dominator_roots := dominator_roots
    |}.

(* Adding new nodes *)

(* 37-43 *)
Definition add_node_aux (t : Dominator_graph.t) (simple : Simple.t)
    : M Dominator_graph.t :=
  let* graph :=
    Simple.Map.update simple
      (fun res =>
        match res with
        | None => ret (Some Simple.Set_.empty)
        | Some _ => ret res
        end)
      t.(Dominator_graph.graph)
  in
  ret
    {| Dominator_graph.required_names := t.(Dominator_graph.required_names);
       Dominator_graph.params_kind := t.(Dominator_graph.params_kind);
       Dominator_graph.graph := graph;
       Dominator_graph.dominator_roots := t.(Dominator_graph.dominator_roots)
    |}.

(* 45-49 *)
Definition add_node (t : Dominator_graph.t) (simple : Simple.t)
    : M Dominator_graph.t :=
  Simple.pattern_match simple
    (fun name _ =>
      let! tmp1 := Name.Set_.mem name t.(Dominator_graph.required_names) in
      if tmp1 then add_node_aux t simple else ret t)
    (fun _ => add_node_aux t simple).

(* Adding roots *)

(* 53-59 *)
Definition add_root (var : Variable_.t) (t : Dominator_graph.t)
    : M Dominator_graph.t :=
  let! tmp1 := Name.var var in
  let! tmp2 := Name.Set_.mem tmp1 t.(Dominator_graph.required_names) in
  if negb tmp2
  then ret t
  else
    let! tmp1 := Simple.var var in
    let! tmp2 := Simple.Set_.add tmp1 t.(Dominator_graph.dominator_roots) in
    ret
      {| Dominator_graph.required_names := t.(Dominator_graph.required_names);
         Dominator_graph.params_kind := t.(Dominator_graph.params_kind);
         Dominator_graph.graph := t.(Dominator_graph.graph);
         Dominator_graph.dominator_roots := tmp2
      |}.

(* Adding edges *)

(* 63-74 *)
Definition add_edge (src : Variable_.t) (dst : Simple.t)
    (t : Dominator_graph.t) : M Dominator_graph.t :=
  let! tmp1 := Name.var src in
  let! tmp2 := Name.Set_.mem tmp1 t.(Dominator_graph.required_names) in
  if negb tmp2
  then ret t
  else
    let* graph :=
      let! tmp1 := Simple.var src in
      Simple.Map.update tmp1
        (fun x =>
          match x with
          | None =>
            let! tmp2 := Simple.Set_.singleton dst in
            ret (Some tmp2)
          | Some s =>
            let! tmp2 := Simple.Set_.add dst s in
            ret (Some tmp2)
          end)
        t.(Dominator_graph.graph)
    in
    ret
      {| Dominator_graph.required_names := t.(Dominator_graph.required_names);
         Dominator_graph.params_kind := t.(Dominator_graph.params_kind);
         Dominator_graph.graph := graph;
         Dominator_graph.dominator_roots :=
           t.(Dominator_graph.dominator_roots)
      |}.

(* Import continuation info into the graph *)

(* 78-131 *)
Definition add_continuation_info
    (map : Continuation.Map.t T.Continuation_info.t) (_k : Continuation.t)
    (elt : T.Continuation_info.t) (t : Dominator_graph.t)
    (return_continuation exn_continuation : Continuation.t)
    : M Dominator_graph.t :=
  (* 80-91 *)
  let* t :=
    let! tmp1 :=
      Bound_parameters.to_list elt.(Flow_types.Continuation_info.params)
    in
    Stdlib_List.fold_left
      (fun t bp =>
        let* var := Bound_parameter.var bp in
        let* t :=
          let! tmp2 := Simple.var var in
          add_node t tmp2
        in
        let* params_kind :=
          let! tmp2 := Bound_parameter.kind bp in
          Variable_.Map.add var tmp2 t.(Dominator_graph.params_kind)
        in
        ret
          {| Dominator_graph.required_names :=
               t.(Dominator_graph.required_names);
             Dominator_graph.params_kind := params_kind;
             Dominator_graph.graph := t.(Dominator_graph.graph);
             Dominator_graph.dominator_roots :=
               t.(Dominator_graph.dominator_roots)
          |})
      t tmp1
  in
  (* 92-96 *)
  let* t :=
    Variable_.Map.fold
      (fun src dst t => add_edge src dst t)
      elt.(Flow_types.Continuation_info.direct_aliases) t
  in
  (* 97-131 *)
  Continuation.Map.fold
    (fun k rewrite_ids t =>
      let! tmp1 := Continuation.equal return_continuation k in
      let! tmp2 := or_else tmp1 (Continuation.equal exn_continuation k) in
      if tmp2
      then ret t
      else
        let* params :=
          match_exn
            (fun _ => Continuation.Map.find k map)
            Not_found
            (fun _ =>
              fatal_errorf2 "Continuation not found during Data_flow: %a@."
                Continuation.print k)
            (fun elt =>
              let! tmp3 :=
                Bound_parameters.vars
                  elt.(Flow_types.Continuation_info.params)
              in
              Array.of_list tmp3)
        in
        Apply_cont_rewrite_id.Map.fold
          (fun _rewrite_id args t =>
            Numeric_types.Int.Map.fold
              (fun i dst t =>
                (* Note on the direction of the edge:

                   We later do a dominator analysis on this graph. To do so, we
                   consider that an edge from ~src to ~dst means: ~dst is used
                   as argument (of an apply_cont), that maps to ~src (as param
                   of a continuation). *)
                let* src := Array.get params i in
                match dst with
                | T.Cont_arg.Simple dst => add_edge src dst t
                | T.Cont_arg.Function_result => add_root src t
                | T.Cont_arg.New_let_binding var _ =>
                  let* t := add_root var t in
                  let! tmp3 := Simple.var var in
                  add_edge src tmp3 t
                end)
              args t)
          rewrite_ids t)
    elt.(Flow_types.Continuation_info.apply_cont_args) t.

(* 133-158. In the compiler: [~required_names ~return_continuation
   ~exn_continuation map]. *)
Definition create (required_names : Name.Set_.t)
    (return_continuation exn_continuation : Continuation.t)
    (map : Continuation.Map.t T.Continuation_info.t)
    : M Dominator_graph.t :=
  let* t := empty required_names in
  (* 135-139: [add_continuation_info ~return_continuation ~exn_continuation
     map] is the function of the arguments that are left. *)
  let* t :=
    Continuation.Map.fold
      (fun k elt t =>
        add_continuation_info map k elt t return_continuation
          exn_continuation)
      map t
  in
  let* all_simples :=
    Simple.Map.fold
      (fun s dsts acc =>
        let! tmp1 := Simple.Set_.union dsts acc in
        Simple.Set_.add s tmp1)
      t.(Dominator_graph.graph) t.(Dominator_graph.dominator_roots)
  in
  (* ensure that all simples are mapped: this is a requirement for the SCC
     computation *)
  let* t :=
    Simple.Set_.fold
      (fun var t =>
        let* graph :=
          Simple.Map.update var
            (fun res =>
              match res with
              | Some _ => ret res
              | None => ret (Some Simple.Set_.empty)
              end)
            t.(Dominator_graph.graph)
        in
        ret
          {| Dominator_graph.required_names :=
               t.(Dominator_graph.required_names);
             Dominator_graph.params_kind := t.(Dominator_graph.params_kind);
             Dominator_graph.graph := graph;
             Dominator_graph.dominator_roots :=
               t.(Dominator_graph.dominator_roots)
          |})
      all_simples t
  in
  ret t.

(* 160-175. [Simple.pattern_match']: the arguments are in the order of the
   interface: [~var ~symbol ~const]. *)
Definition find_dom (simple : Simple.t) (doms : alias_map) : M Simple.t :=
  Simple.pattern_match' simple
    (fun var _ =>
      (* there are two cases where the variable is not in the "doms" maps:

         - is not mapped in the graph, which means that it is a let-bound
         variable, in which case it can only be dominated by itself.

         - we are in the first iteration of a loop fixpoint, in which case we
         also want to initialize the dominator to the variable itself. *)
      let! tmp1 := Variable_.Map.find_or_null var doms in
      match tmp1 with
      | Or_null.Null => ret simple
      | Or_null.This dom => ret dom
      end)
    (* Symbols and constants are always their own dominators *)
    (fun _ _ => ret simple)
    (fun _ => ret simple).

(* 177-193. The compiler's first parameter is the pattern
   [{ dominator_roots; graph; _ }]. *)
Definition update_doms_for_one_var (t : Dominator_graph.t) (doms : alias_map)
    (var : Variable_.t) : M alias_map :=
  let* '{| Dominator_graph.dominator_roots := dominator_roots;
           Dominator_graph.graph := graph
        |} :=
    ret t
  in
  let* simple := Simple.var var in
  let* dom :=
    let! tmp1 := Simple.Set_.mem simple dominator_roots in
    if tmp1
    then ret simple
    else
      let! tmp2 := Simple.Map.find_or_null simple graph in
      match tmp2 with
      | Or_null.Null => ret simple
      | Or_null.This predecessors =>
        let* s :=
          Simple.Set_.map
            (fun predecessor => find_dom predecessor doms)
            predecessors
        in
        let! tmp3 := Simple.Set_.get_singleton s in
        match tmp3 with Some ret_ => ret ret_ | None => ret simple end
      end
  in
  Variable_.Map.add var dom doms.

(* 195-218. The compiler's first parameter is the pattern [{ graph; _ }]. *)
Definition initialize_doms_for_fixpoint (t : Dominator_graph.t)
    (doms : alias_map) (simples : list Simple.t)
    : M (Simple.Map.t Simple.Set_.t) :=
  let* '{| Dominator_graph.graph := graph |} := ret t in
  (* Note: since all simples are in a cycle, all_predecessors will include all
     of the simples from the cycle. Also, since we're a in a cycle, all simples
     should actually be variables. *)
  let* all_predecessors :=
    Stdlib_List.fold_left
      (fun acc var =>
        let* predecessors :=
          try_with
            (fun _ => Simple.Map.find var graph)
            Not_found
            (fun _ => assert_false)
        in
        Simple.Set_.union predecessors acc)
      Simple.Set_.empty simples
  in
  let* init_doms :=
    Simple.Set_.map (fun simple => find_dom simple doms) all_predecessors
  in
  let* outside_cycle :=
    let! tmp1 := Simple.Set_.of_list simples in
    let! tmp2 := Simple.Set_.diff all_predecessors tmp1 in
    Simple.Map.of_set
      (fun simple =>
        let! tmp3 := find_dom simple doms in
        Simple.Set_.singleton tmp3)
      tmp2
  in
  Stdlib_List.fold_left
    (fun doms simple => Simple.Map.add simple init_doms doms)
    outside_cycle simples.

(* 220-243. The compiler's first parameter is the pattern
   [({ graph; dominator_roots; _ } as t)]. *)
Fixpoint dom_fixpoint (fuel : fuel) (t : Dominator_graph.t)
    (acc : Simple.Map.t Simple.Set_.t) (simples : list Simple.t)
    {struct fuel} : M (Simple.Map.t Simple.Set_.t) :=
  recursive! fuel in
  let* '{| Dominator_graph.graph := graph;
           Dominator_graph.dominator_roots := dominator_roots
        |} :=
    ret t
  in
  let* acc' :=
    Stdlib_List.fold_left
      (fun acc simple =>
        let! tmp1 := Simple.Set_.mem simple dominator_roots in
        if tmp1
        then
          let! tmp2 := Simple.Set_.singleton simple in
          Simple.Map.add simple tmp2 acc
        else
          let* init_doms := Simple.Map.find simple acc in
          let* predecessors :=
            try_with
              (fun _ => Simple.Map.find simple graph)
              Not_found
              (fun _ => assert_false)
          in
          let* new_doms :=
            Simple.Set_.fold
              (fun predecessor new_doms =>
                let! tmp2 := Simple.Map.find predecessor acc in
                Simple.Set_.inter new_doms tmp2)
              predecessors init_doms
          in
          let* new_doms := Simple.Set_.add simple new_doms in
          Simple.Map.add simple new_doms acc)
      acc simples
  in
  let! tmp1 := Simple.Map.equal Simple.Set_.equal acc acc' in
  if tmp1 then ret acc else dom_fixpoint fuel t acc' simples.

(* 245-265 *)
Definition extract_doms (doms : alias_map)
    (fixpoint_result : Simple.Map.t Simple.Set_.t) (simples : list Simple.t)
    : M alias_map :=
  let* simple_set := Simple.Set_.of_list simples in
  Stdlib_List.fold_left
    (fun doms simple =>
      let* var :=
        Simple.pattern_match' simple
          (fun v _ => ret v)
          (fun _ _ =>
            fatal_errorf0
              "Cycles in the dominator analysis should never contain symbols")
          (fun _ =>
            fatal_errorf0
              "Cycles in the dominator analysis should never contain constants")
      in
      let* fixpoint_doms := Simple.Map.find simple fixpoint_result in
      let* var_doms := Simple.Set_.diff fixpoint_doms simple_set in
      let* cardinal := Simple.Set_.cardinal var_doms in
      assert_ (cardinal <=? 1) ;;
      let* dom :=
        if cardinal =? 1 then Simple.Set_.choose var_doms else ret simple
      in
      Variable_.Map.add var dom doms)
    doms simples.

(* 267-285. The compiler's parameter is the pattern [({ graph; _ } as t)]. *)
Definition dominator_analysis (t : Dominator_graph.t) : M alias_map :=
  let* '{| Dominator_graph.graph := graph |} := ret t in
  let* components := G.connected_components_sorted_from_roots_to_leaf graph in
  let* dominators :=
    Array.fold_right
      (fun component doms =>
        match component with
        | G.No_loop simple =>
          Simple.pattern_match' simple
            (fun var _ => update_doms_for_one_var t doms var)
            (fun _ _ => ret doms)
            (fun _ => ret doms)
        | G.Has_loop simples =>
          let* loop_doms := initialize_doms_for_fixpoint t doms simples in
          let* loop_result :=
            let_fuel! fuel in
            dom_fixpoint fuel t loop_doms simples
          in
          let* doms := extract_doms doms loop_result simples in
          ret doms
        end)
      components Variable_.Map.empty
  in
  ret dominators.

(* 287-308. The compiler's first parameter is the pattern
   [{ params_kind; required_names; _ }]. *)
Definition aliases_kind (t : Dominator_graph.t) (aliases : alias_map)
    : M (Variable_.Map.t Flambda_kind.t) :=
  let* '{| Dominator_graph.params_kind := params_kind;
           Dominator_graph.required_names := required_names
        |} :=
    ret t
  in
  Variable_.Map.fold
    (fun param kind acc =>
      let! tmp1 := Name.var param in
      let! tmp2 := Name.Set_.mem tmp1 required_names in
      if negb tmp2
      then ret acc
      else
        let* alias := Variable_.Map.find param aliases in
        (* CR: Not sure this is absolutely necessary, but it's simpler. The
           alternative would be to do a join of all kinds with subkinds for all
           the members of the alias class. *)
        let* kind := Flambda_kind.With_subkind.kind kind in
        Simple.pattern_match' alias
          (fun v _ =>
            (let! tmp1 := Variable_.Map.find_or_null v acc in
             match tmp1 with
             | Or_null.Null => ret tt
             | Or_null.This alias_kind =>
               let! tmp2 := Flambda_kind.equal kind alias_kind in
               if negb tmp2
               then fatal_errorf0 "Incoherent kinds for aliases !"
               else ret tt
             end) ;;
            Variable_.Map.add v kind acc)
          (fun _ _ => ret acc)
          (fun _ => ret acc))
    params_kind Variable_.Map.empty.

(* PORT-GAP(decl): 312, the coercion [(simple :> int)] of the private type
   [Simple.t]: no function of the compiler, so no declaration in decl/; its
   OCaml text. *)
Parameter simple_to_int : Simple.t -> int.
Extract Inlined Constant simple_to_int =>
  "(fun (simple : Simple.t) -> (simple :> int))".

(* 310-359 *)
Module Dot.
  (* 311-312 *)
  Definition node_id (ctx : int) (ppf : Format.formatter) (simple : Simple.t)
      : M unit :=
    Format.fprintf2 ppf "node_%d_%d" ctx (simple_to_int simple).

  (* 314-321 *)
  Definition node (ctx : int) (root : bool) (ppf : Format.formatter)
      (simple : Simple.t) : M unit :=
    if root
    then
      Format.fprintf4 ppf "%a [shape=record label=""%a""];@
" (node_id ctx) simple Simple.print simple
    else
      Format.fprintf4 ppf "%a [label=""%a""];@
" (node_id ctx) simple Simple.print simple.

  (* 323-333 *)
  Definition nodes {A : Type} (ctx : int) (roots : Simple.Set_.t)
      (ppf : Format.formatter) (map : Simple.Map.t A) : M unit :=
    Simple.Map.iter
      (fun simple _ =>
        let* root :=
          Simple.pattern_match' simple
            (fun _ _ => Simple.Set_.mem simple roots)
            (fun _ _ => ret true)
            (fun _ => ret true)
        in
        node ctx root ppf simple)
      map.

  (* 335-337 *)
  Definition edge (ctx : int) (color : string) (ppf : Format.formatter)
      (src dst : Simple.t) : M unit :=
    Format.fprintf5 ppf "%a -> %a [color=""%s""];@
" (node_id ctx) src (node_id ctx) dst color.

  (* 339-343 *)
  Definition edges (ctx : int) (color : string) (ppf : Format.formatter)
      (edge_map : Simple.Map.t Simple.Set_.t) : M unit :=
    Simple.Map.iter
      (fun src dst_set =>
        Simple.Set_.iter (fun dst => edge ctx color ppf src dst) dst_set)
      edge_map.

  (* 345-348 *)
  Definition edges' (ctx : int) (color : string) (ppf : Format.formatter)
      (edge_map : Variable_.Map.t Simple.t) : M unit :=
    Variable_.Map.iter
      (fun src dst =>
        let! tmp1 := Simple.var src in
        edge ctx color ppf tmp1 dst)
      edge_map.

  (* 350-358 *)
  Definition print (ctx : int) (print_name : string) (doms : alias_map)
      (ppf : Format.formatter) (t : Dominator_graph.t) : M unit :=
    Flambda_colours.without_colours (fun _ =>
      Format.fprintf8 ppf "subgraph cluster_%d { label=""%s""@
%a@
%a@
%a@
}@." ctx print_name
        (nodes (A:=Simple.Set_.t) ctx t.(Dominator_graph.dominator_roots))
        t.(Dominator_graph.graph)
        (edges ctx "black")
        t.(Dominator_graph.graph)
        (edges' ctx "red")
        doms).
End Dot.
