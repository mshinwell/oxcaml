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

(* This file follows middle_end/flambda2/simplify/flow/data_flow_graph.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, function by function
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the fuel of the recursive functions)
   is that of GUIDE.md; the functor [Edge] of the file is a function of the
   operations that it uses. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Array Bound_parameters
  Code_id Continuation Flambda2_types Flambda_primitive Flow_types Format
  List Name Name_mode Name_occurrences Numeric_types Or_unknown Queue Simple
  Value_slot Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Flow_types.Mutable_prim.t *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 15 *)
From SimplifyPort.abbrev.data_flow_graph Require Import Port_abbreviations.
(*OCAML
module T = Flow_types
OCAML*)

(* 17-26 *)
Record t : Type :=
  { code_age_relation : Flambda2_types.Code_age_relation.t;
    name_to_name : Name.Map.t Name.Set_.t;
    name_to_code_id : Name.Map.t Code_id.Set_.t;
    code_id_to_name : Code_id.Map.t Name.Set_.t;
    code_id_to_code_id : Code_id.Map.t Code_id.Set_.t;
    unconditionally_used : Name.Set_.t;
    code_id_unconditionally_used : Code_id.Set_.t;
    is_toplevel : bool
  }.

(* 28-146 *)
Module Reachable.
  (* PORT-GAP(loose): 29-46, the functor [Edge (Src_map) (Dst_set)]: its one
     function [push] takes the five members of [Src_map] and [Dst_set] that
     it uses as its first arguments; the types [src] and [dst] of the
     functor, and its attribute [@@inline], are not kept. *)
  (* TODO check that this applied here *)
  Module Edge.
    (* 35-44 *)
    Definition push {Src Dst Dst_set_t Src_map_t : Type}
        (Src_map_find : Src -> Src_map_t -> M Dst_set_t)
        (Dst_set_empty : Dst_set_t)
        (Dst_set_diff : Dst_set_t -> Dst_set_t -> M Dst_set_t)
        (Dst_set_iter : (Dst -> M unit) -> Dst_set_t -> M unit)
        (Dst_set_union : Dst_set_t -> Dst_set_t -> M Dst_set_t)
        (src : Src) (enqueued : Dst_set_t) (queue : Queue.t Dst)
        (graph : Src_map_t) : M Dst_set_t :=
      let* neighbours :=
        match_exn
          (fun _ => Src_map_find src graph)
          Not_found
          (fun _ => ret Dst_set_empty)
          (fun set => ret set)
      in
      let* new_neighbours := Dst_set_diff neighbours enqueued in
      Dst_set_iter (fun dst => Queue.push dst queue) new_neighbours ;;
      Dst_set_union enqueued new_neighbours.
  End Edge.

  (* PORT-GAP(loose): 49, [Edge (Name.Map) (Name.Set)]: the function of the
     functor with the members of the two modules. *)
  Module Name_Name_Edge.
    Definition push (src : Name.t) (enqueued : Name.Set_.t)
        (queue : Queue.t Name.t) (graph : Name.Map.t Name.Set_.t)
        : M Name.Set_.t :=
      Edge.push Name.Map.find Name.Set_.empty Name.Set_.diff Name.Set_.iter
        Name.Set_.union src enqueued queue graph.
  End Name_Name_Edge.

  (* PORT-GAP(loose): 50, [Edge (Name.Map) (Code_id.Set)], as above. *)
  Module Name_Code_id_Edge.
    Definition push (src : Name.t) (enqueued : Code_id.Set_.t)
        (queue : Queue.t Code_id.t) (graph : Name.Map.t Code_id.Set_.t)
        : M Code_id.Set_.t :=
      Edge.push Name.Map.find Code_id.Set_.empty Code_id.Set_.diff
        Code_id.Set_.iter Code_id.Set_.union src enqueued queue graph.
  End Name_Code_id_Edge.

  (* PORT-GAP(loose): 51, [Edge (Code_id.Map) (Name.Set)], as above. *)
  Module Code_id_Name_Edge.
    Definition push (src : Code_id.t) (enqueued : Name.Set_.t)
        (queue : Queue.t Name.t) (graph : Code_id.Map.t Name.Set_.t)
        : M Name.Set_.t :=
      Edge.push Code_id.Map.find Name.Set_.empty Name.Set_.diff
        Name.Set_.iter Name.Set_.union src enqueued queue graph.
  End Code_id_Name_Edge.

  (* PORT-GAP(loose): 52, [Edge (Code_id.Map) (Code_id.Set)], as above. *)
  Module Code_id_Code_id_Edge.
    Definition push (src : Code_id.t) (enqueued : Code_id.Set_.t)
        (queue : Queue.t Code_id.t) (graph : Code_id.Map.t Code_id.Set_.t)
        : M Code_id.Set_.t :=
      Edge.push Code_id.Map.find Code_id.Set_.empty Code_id.Set_.diff
        Code_id.Set_.iter Code_id.Set_.union src enqueued queue graph.
  End Code_id_Code_id_Edge.

  (* breadth-first reachability analysis. *)
  (* 55-87 *)
  Fixpoint reachable_names (fuel : fuel) (t : Data_flow_graph.t)
      (code_id_queue : Queue.t Code_id.t) (code_id_enqueued : Code_id.Set_.t)
      (older_enqueued : Code_id.Set_.t) (name_queue : Queue.t Name.t)
      (name_enqueued : Name.Set_.t) {struct fuel}
      : M T.Data_flow_result.t :=
    recursive! fuel in
    match_exn
      (fun _ => Queue.take name_queue)
      Queue.Empty
      (fun _ =>
        if t.(Data_flow_graph.is_toplevel)
        then
          let! tmp1 := Queue.is_empty code_id_queue in
          if tmp1
          then
            ret
              {| T.Data_flow_result.required_names := name_enqueued;
                 T.Data_flow_result.reachable_code_ids :=
                   Or_unknown.Known
                     {| T.Reachable_code_ids.live_code_ids :=
                          code_id_enqueued;
                        T.Reachable_code_ids.ancestors_of_live_code_ids :=
                          older_enqueued
                     |}
              |}
          else
            let! tmp2 := Queue.create tt in
            reachable_code_ids fuel t code_id_queue code_id_enqueued tmp2
              older_enqueued name_queue name_enqueued
        else
          ret
            {| T.Data_flow_result.required_names := name_enqueued;
               T.Data_flow_result.reachable_code_ids := Or_unknown.Unknown
            |})
      (fun src =>
        let* name_enqueued :=
          Name_Name_Edge.push src name_enqueued name_queue
            t.(Data_flow_graph.name_to_name)
        in
        let* code_id_enqueued :=
          Name_Code_id_Edge.push src code_id_enqueued code_id_queue
            t.(Data_flow_graph.name_to_code_id)
        in
        reachable_names fuel t code_id_queue code_id_enqueued older_enqueued
          name_queue name_enqueued)

  (* 89-116 *)
  with reachable_code_ids (fuel : fuel) (t : Data_flow_graph.t)
      (code_id_queue : Queue.t Code_id.t) (code_id_enqueued : Code_id.Set_.t)
      (older_queue : Queue.t Code_id.t) (older_enqueued : Code_id.Set_.t)
      (name_queue : Queue.t Name.t) (name_enqueued : Name.Set_.t)
      {struct fuel} : M T.Data_flow_result.t :=
    recursive! fuel in
    match_exn
      (fun _ => Queue.take code_id_queue)
      Queue.Empty
      (fun _ =>
        let! tmp1 := Queue.is_empty older_queue in
        if tmp1
        then
          reachable_names fuel t code_id_queue code_id_enqueued older_enqueued
            name_queue name_enqueued
        else
          reachable_older_code_ids fuel t code_id_queue code_id_enqueued
            older_queue older_enqueued name_queue name_enqueued)
      (fun src =>
        let* name_enqueued :=
          Code_id_Name_Edge.push src name_enqueued name_queue
            t.(Data_flow_graph.code_id_to_name)
        in
        let* code_id_enqueued :=
          Code_id_Code_id_Edge.push src code_id_enqueued code_id_queue
            t.(Data_flow_graph.code_id_to_code_id)
        in
        let* older_enqueued :=
          let! tmp1 := Code_id.Set_.mem src older_enqueued in
          if tmp1
          then ret older_enqueued
          else (
            Queue.push src older_queue ;;
            Code_id.Set_.add src older_enqueued)
        in
        reachable_code_ids fuel t code_id_queue code_id_enqueued older_queue
          older_enqueued name_queue name_enqueued)

  (* 118-145 *)
  with reachable_older_code_ids (fuel : fuel) (t : Data_flow_graph.t)
      (code_id_queue : Queue.t Code_id.t) (code_id_enqueued : Code_id.Set_.t)
      (older_queue : Queue.t Code_id.t) (older_enqueued : Code_id.Set_.t)
      (name_queue : Queue.t Name.t) (name_enqueued : Name.Set_.t)
      {struct fuel} : M T.Data_flow_result.t :=
    recursive! fuel in
    match_exn
      (fun _ => Queue.take older_queue)
      Queue.Empty
      (fun _ =>
        reachable_code_ids fuel t code_id_queue code_id_enqueued older_queue
          older_enqueued name_queue name_enqueued)
      (fun src =>
        let! tmp1 :=
          Flambda2_types.Code_age_relation.get_older_version_of
            t.(Data_flow_graph.code_age_relation) src
        in
        match tmp1 with
        | None =>
          reachable_older_code_ids fuel t code_id_queue code_id_enqueued
            older_queue older_enqueued name_queue name_enqueued
        | Some dst =>
          let! tmp2 := Code_id.Set_.mem dst older_enqueued in
          if tmp2
          then
            let! tmp3 := Code_id.Set_.mem dst code_id_enqueued in
            if tmp3
            then
              reachable_older_code_ids fuel t code_id_queue code_id_enqueued
                older_queue older_enqueued name_queue name_enqueued
            else
              let* code_id_enqueued :=
                Code_id.Set_.add dst code_id_enqueued
              in
              Queue.push dst code_id_queue ;;
              reachable_older_code_ids fuel t code_id_queue code_id_enqueued
                older_queue older_enqueued name_queue name_enqueued
          else
            let* older_enqueued := Code_id.Set_.add dst older_enqueued in
            Queue.push dst older_queue ;;
            reachable_older_code_ids fuel t code_id_queue code_id_enqueued
              older_queue older_enqueued name_queue name_enqueued
        end).
End Reachable.

(* 148-157 *)
Definition empty (code_age_relation : Flambda2_types.Code_age_relation.t)
    (is_toplevel : bool) (code_ids_to_never_delete : Code_id.Set_.t)
    : M Data_flow_graph.t :=
  ret
    {| Data_flow_graph.code_age_relation := code_age_relation;
       Data_flow_graph.is_toplevel := is_toplevel;
       Data_flow_graph.name_to_name := Name.Map.empty;
       Data_flow_graph.name_to_code_id := Name.Map.empty;
       Data_flow_graph.code_id_to_name := Code_id.Map.empty;
       Data_flow_graph.code_id_to_code_id := Code_id.Map.empty;
       Data_flow_graph.unconditionally_used := Name.Set_.empty;
       Data_flow_graph.code_id_unconditionally_used :=
         code_ids_to_never_delete
    |}.

(* 159-184. The compiler's second parameter is the pattern of all the
   fields. *)
Definition print (ppf : Format.formatter) (t : Data_flow_graph.t) : M unit :=
  let* '{| Data_flow_graph.is_toplevel := is_toplevel;
           Data_flow_graph.name_to_name := name_to_name;
           Data_flow_graph.name_to_code_id := name_to_code_id;
           Data_flow_graph.code_id_to_name := code_id_to_name;
           Data_flow_graph.code_id_to_code_id := code_id_to_code_id;
           Data_flow_graph.code_age_relation := code_age_relation;
           Data_flow_graph.unconditionally_used := unconditionally_used;
           Data_flow_graph.code_id_unconditionally_used :=
             code_id_unconditionally_used
        |} :=
    ret t
  in
  (* 176-182 *)
  let! tmp1 := papp1 Code_id.Map.print Code_id.Set_.print in
  let! tmp2 := papp1 Code_id.Map.print Name.Set_.print in
  let! tmp3 := papp1 Name.Map.print Code_id.Set_.print in
  let! tmp4 := papp1 Name.Map.print Name.Set_.print in
  Format.fprintf15 ppf
    "@[<hov 1>(@[<hov 1>(is_toplevel %b)@]@ @[<hov 1>(code_age_relation@ %a)@]@ @[<hov 1>(name_to_name@ %a)@]@ @[<hov 1>(name_to_code_id@ %a)@]@ @[<hov 1>(code_id_to_name@ %a)@]@ @[<hov 1>(code_id_to_code_id@ %a)@]@ @[<hov 1>(unconditionally_used@ %a)@]@ @[<hov 1>(code_id_unconditionally_used@ %a)@])@]"
    is_toplevel Flambda2_types.Code_age_relation.print code_age_relation
    tmp4
    name_to_name
    tmp3
    name_to_code_id
    tmp2
    code_id_to_name
    tmp1
    code_id_to_code_id Name.Set_.print unconditionally_used Code_id.Set_.print
    code_id_unconditionally_used.

(* *)
(* 187-189. In the compiler: [name_occurrences ~init ~names ~code_ids]. *)
Definition fold_name_occurrences {A : Type}
    (name_occurrences : Name_occurrences.t) (init : A)
    (names : A -> Name.t -> M A) (code_ids : A -> Code_id.Set_.t -> M A)
    : M A :=
  let! tmp1 := Name_occurrences.code_ids name_occurrences in
  let! tmp2 := code_ids init tmp1 in
  Name_occurrences.fold_names name_occurrences tmp2 names.

(* PORT-GAP(update): 202, [{ t with name_to_code_id }]. *)
Definition update_name_to_code_id (t : Data_flow_graph.t)
    (name_to_code_id : Name.Map.t Code_id.Set_.t) : Data_flow_graph.t :=
  {| Data_flow_graph.code_age_relation := t.(Data_flow_graph.code_age_relation);
     Data_flow_graph.name_to_name := t.(Data_flow_graph.name_to_name);
     Data_flow_graph.name_to_code_id := name_to_code_id;
     Data_flow_graph.code_id_to_name := t.(Data_flow_graph.code_id_to_name);
     Data_flow_graph.code_id_to_code_id :=
       t.(Data_flow_graph.code_id_to_code_id);
     Data_flow_graph.unconditionally_used :=
       t.(Data_flow_graph.unconditionally_used);
     Data_flow_graph.code_id_unconditionally_used :=
       t.(Data_flow_graph.code_id_unconditionally_used);
     Data_flow_graph.is_toplevel := t.(Data_flow_graph.is_toplevel)
  |}.
Extract Inlined Constant update_name_to_code_id =>
  "(fun t name_to_code_id -> { t with name_to_code_id = name_to_code_id })".

(* Some auxiliary functions *)
(* 192-202. The compiler's last parameter is the pattern
   [({ name_to_code_id; _ } as t)]. *)
Definition add_code_id_dep (src : Name.t) (dst : Code_id.Set_.t)
    (t : Data_flow_graph.t) : M Data_flow_graph.t :=
  let* '{| Data_flow_graph.name_to_code_id := name_to_code_id |} := ret t in
  let* name_to_code_id :=
    Name.Map.update src
      (fun x =>
        match x with
        | None =>
          let! tmp1 := Code_id.Set_.is_empty dst in
          if tmp1 then ret None else ret (Some dst)
        | Some old =>
          fatal_errorf6 "Same name bound multiple times: %a -> %a, %a"
            Name.print src Code_id.Set_.print old Code_id.Set_.print dst
        end)
      name_to_code_id
  in
  ret (update_name_to_code_id t name_to_code_id).

(* PORT-GAP(update): 212, [{ t with name_to_name }]. *)
Definition update_name_to_name (t : Data_flow_graph.t)
    (name_to_name : Name.Map.t Name.Set_.t) : Data_flow_graph.t :=
  {| Data_flow_graph.code_age_relation := t.(Data_flow_graph.code_age_relation);
     Data_flow_graph.name_to_name := name_to_name;
     Data_flow_graph.name_to_code_id := t.(Data_flow_graph.name_to_code_id);
     Data_flow_graph.code_id_to_name := t.(Data_flow_graph.code_id_to_name);
     Data_flow_graph.code_id_to_code_id :=
       t.(Data_flow_graph.code_id_to_code_id);
     Data_flow_graph.unconditionally_used :=
       t.(Data_flow_graph.unconditionally_used);
     Data_flow_graph.code_id_unconditionally_used :=
       t.(Data_flow_graph.code_id_unconditionally_used);
     Data_flow_graph.is_toplevel := t.(Data_flow_graph.is_toplevel)
  |}.
Extract Inlined Constant update_name_to_name =>
  "(fun t name_to_name -> { t with name_to_name = name_to_name })".

(* 204-212. The compiler's last parameter is the pattern
   [({ name_to_name; _ } as t)]. *)
Definition add_dependency (src dst : Name.t) (t : Data_flow_graph.t)
    : M Data_flow_graph.t :=
  let* '{| Data_flow_graph.name_to_name := name_to_name |} := ret t in
  let* name_to_name :=
    Name.Map.update src
      (fun x =>
        match x with
        | None =>
          let! tmp1 := Name.Set_.singleton dst in
          ret (Some tmp1)
        | Some set =>
          let! tmp1 := Name.Set_.add dst set in
          ret (Some tmp1)
        end)
      name_to_name
  in
  ret (update_name_to_name t name_to_name).

(* PORT-GAP(update): 222, [{ t with code_id_to_name }]. *)
Definition update_code_id_to_name (t : Data_flow_graph.t)
    (code_id_to_name : Code_id.Map.t Name.Set_.t) : Data_flow_graph.t :=
  {| Data_flow_graph.code_age_relation := t.(Data_flow_graph.code_age_relation);
     Data_flow_graph.name_to_name := t.(Data_flow_graph.name_to_name);
     Data_flow_graph.name_to_code_id := t.(Data_flow_graph.name_to_code_id);
     Data_flow_graph.code_id_to_name := code_id_to_name;
     Data_flow_graph.code_id_to_code_id :=
       t.(Data_flow_graph.code_id_to_code_id);
     Data_flow_graph.unconditionally_used :=
       t.(Data_flow_graph.unconditionally_used);
     Data_flow_graph.code_id_unconditionally_used :=
       t.(Data_flow_graph.code_id_unconditionally_used);
     Data_flow_graph.is_toplevel := t.(Data_flow_graph.is_toplevel)
  |}.
Extract Inlined Constant update_code_id_to_name =>
  "(fun t code_id_to_name -> { t with code_id_to_name = code_id_to_name })".

(* 214-222. The compiler's last parameter is the pattern
   [({ code_id_to_name; _ } as t)]. *)
Definition add_code_id_dependency (src : Code_id.t) (dst : Name.t)
    (t : Data_flow_graph.t) : M Data_flow_graph.t :=
  let* '{| Data_flow_graph.code_id_to_name := code_id_to_name |} := ret t in
  let* code_id_to_name :=
    Code_id.Map.update src
      (fun x =>
        match x with
        | None =>
          let! tmp1 := Name.Set_.singleton dst in
          ret (Some tmp1)
        | Some set =>
          let! tmp1 := Name.Set_.add dst set in
          ret (Some tmp1)
        end)
      code_id_to_name
  in
  ret (update_code_id_to_name t code_id_to_name).

(* PORT-GAP(update): 234, [{ t with code_id_to_code_id }]. *)
Definition update_code_id_to_code_id (t : Data_flow_graph.t)
    (code_id_to_code_id : Code_id.Map.t Code_id.Set_.t) : Data_flow_graph.t :=
  {| Data_flow_graph.code_age_relation := t.(Data_flow_graph.code_age_relation);
     Data_flow_graph.name_to_name := t.(Data_flow_graph.name_to_name);
     Data_flow_graph.name_to_code_id := t.(Data_flow_graph.name_to_code_id);
     Data_flow_graph.code_id_to_name := t.(Data_flow_graph.code_id_to_name);
     Data_flow_graph.code_id_to_code_id := code_id_to_code_id;
     Data_flow_graph.unconditionally_used :=
       t.(Data_flow_graph.unconditionally_used);
     Data_flow_graph.code_id_unconditionally_used :=
       t.(Data_flow_graph.code_id_unconditionally_used);
     Data_flow_graph.is_toplevel := t.(Data_flow_graph.is_toplevel)
  |}.
Extract Inlined Constant update_code_id_to_code_id =>
  "(fun t code_id_to_code_id -> { t with code_id_to_code_id =
   code_id_to_code_id })".

(* 224-234. The compiler's last parameter is the pattern
   [({ code_id_to_code_id; _ } as t)]. *)
Definition add_code_id_to_code_id (src : Code_id.t) (dst : Code_id.Set_.t)
    (t : Data_flow_graph.t) : M Data_flow_graph.t :=
  let* '{| Data_flow_graph.code_id_to_code_id := code_id_to_code_id |} :=
    ret t
  in
  let* code_id_to_code_id :=
    Code_id.Map.update src
      (fun x =>
        match x with
        | None =>
          let! tmp1 := Code_id.Set_.is_empty dst in
          if tmp1 then ret None else ret (Some dst)
        | Some old =>
          fatal_errorf6 "Same code_id bound multiple times: %a -> %a, %a"
            Code_id.print src Code_id.Set_.print old Code_id.Set_.print dst
        end)
      code_id_to_code_id
  in
  ret (update_code_id_to_code_id t code_id_to_code_id).

(* PORT-GAP(update): 248, [{ t with unconditionally_used;
   code_id_unconditionally_used }]. *)
Definition update_unconditionally_used_code_id_unconditionally_used
    (t : Data_flow_graph.t) (unconditionally_used : Name.Set_.t)
    (code_id_unconditionally_used : Code_id.Set_.t) : Data_flow_graph.t :=
  {| Data_flow_graph.code_age_relation := t.(Data_flow_graph.code_age_relation);
     Data_flow_graph.name_to_name := t.(Data_flow_graph.name_to_name);
     Data_flow_graph.name_to_code_id := t.(Data_flow_graph.name_to_code_id);
     Data_flow_graph.code_id_to_name := t.(Data_flow_graph.code_id_to_name);
     Data_flow_graph.code_id_to_code_id :=
       t.(Data_flow_graph.code_id_to_code_id);
     Data_flow_graph.unconditionally_used := unconditionally_used;
     Data_flow_graph.code_id_unconditionally_used :=
       code_id_unconditionally_used;
     Data_flow_graph.is_toplevel := t.(Data_flow_graph.is_toplevel)
  |}.
Extract Inlined Constant
    update_unconditionally_used_code_id_unconditionally_used =>
  "(fun t unconditionally_used code_id_unconditionally_used -> { t with
   unconditionally_used = unconditionally_used; code_id_unconditionally_used =
   code_id_unconditionally_used })".

(* 236-248. The compiler's last parameter is the pattern
   [({ unconditionally_used; code_id_unconditionally_used; _ } as t)]. *)
Definition add_name_occurrences (name_occurrences : Name_occurrences.t)
    (t : Data_flow_graph.t) : M Data_flow_graph.t :=
  let* '{| Data_flow_graph.unconditionally_used := unconditionally_used;
           Data_flow_graph.code_id_unconditionally_used :=
             code_id_unconditionally_used
        |} :=
    ret t
  in
  let* unconditionally_used :=
    Name_occurrences.fold_names name_occurrences unconditionally_used
      (fun set name => Name.Set_.add name set)
  in
  let* code_id_unconditionally_used :=
    let! tmp1 := Name_occurrences.code_ids name_occurrences in
    Code_id.Set_.union tmp1 code_id_unconditionally_used
  in
  ret
    (update_unconditionally_used_code_id_unconditionally_used t
      unconditionally_used code_id_unconditionally_used).

(* 250-412. In the compiler the fifth parameter is [_] and the sixth is the
   pattern of all the fields of [T.Continuation_info.t]. *)
Definition add_continuation_info
    (map : Continuation.Map.t T.Continuation_info.t)
    (return_continuation exn_continuation : Continuation.t)
    (used_value_slots : Or_unknown.t Name_occurrences.t)
    (_k : Continuation.t) (elt : T.Continuation_info.t)
    (t : Data_flow_graph.t) : M Data_flow_graph.t :=
  let* '{| T.Continuation_info.apply_cont_args := apply_cont_args;
           (* CR pchambart: properly follow dependencies in exception extra
              args. They are currently marked as always used, so it is
              correct, but not optimal *)
           T.Continuation_info.used_in_handler := used_in_handler;
           T.Continuation_info.bindings := bindings;
           T.Continuation_info.direct_aliases := direct_aliases;
           T.Continuation_info.mutable_let_prims_rev := mutable_let_prims_rev;
           T.Continuation_info.defined := _;
           T.Continuation_info.code_ids := code_ids;
           T.Continuation_info.value_slots := value_slots;
           T.Continuation_info.continuation := _;
           T.Continuation_info.recursive := _;
           T.Continuation_info.is_exn_handler := _;
           T.Continuation_info.parent_continuation := _;
           T.Continuation_info.params := _
        |} :=
    ret elt
  in
  (* Add the vars used in the handler *)
  let* t := add_name_occurrences used_in_handler t in
  (* Add the dependencies created by closures vars in envs *)
  (* 273-278 *)
  let* is_value_slot_used :=
    match used_value_slots with
    | Or_unknown.Unknown => ret (fun (_ : Value_slot.t) => ret true)
    | Or_unknown.Known used_value_slots =>
      papp1 Name_occurrences.value_slot_is_used_or_imported used_value_slots
    end
  in
  (* 279-293 *)
  let* t :=
    Value_slot.Map.fold
      (fun value_slot map t =>
        let! tmp1 := is_value_slot_used value_slot in
        if negb tmp1
        then ret t
        else
          Name.Map.fold
            (fun closure_name values_in_env t =>
              Name_occurrences.fold_names values_in_env t
                (fun t value_in_env =>
                  add_dependency closure_name value_in_env t))
            map t)
      value_slots t
  in
  (* Build the graph of dependencies between names *)
  (* 295-302 *)
  let* t :=
    Name.Map.fold
      (fun src name_occurrences graph =>
        fold_name_occurrences name_occurrences graph
          (fun t dst => add_dependency src dst t)
          (fun t dst => add_code_id_dep src dst t))
      bindings t
  in
  (* 303-312 *)
  let* t :=
    Variable_.Map.fold
      (fun src simple graph =>
        let* src := Name.var src in
        let* name_occurrences := Simple.free_names simple in
        fold_name_occurrences name_occurrences graph
          (fun t dst => add_dependency src dst t)
          (fun t dst => add_code_id_dep src dst t))
      direct_aliases t
  in
  (* 313-333: the second argument of the function is the pattern
     [T.Mutable_let_prim.{ bound_var; prim; original_prim; named_rewrite_id =
     _ }]. *)
  let* t :=
    List.fold_left
      (fun t pat =>
        let* '{| T.Mutable_let_prim.bound_var := bound_var;
                 T.Mutable_let_prim.prim := prim;
                 T.Mutable_let_prim.original_prim := original_prim;
                 T.Mutable_let_prim.named_rewrite_id := _
              |} :=
          ret pat
        in
        let* src := Name.var bound_var in
        (* This is an over-aproximation of the the dependencies after mutable
           unboxing, but: if no unboxing happen this is the correct
           dependencies, if some unboxing happens, then we will run a second
           round of optimisation on the current function (if this is the code of
           a function) that will actually remove those spurious dependencies *)
        match prim with
        | T.Mutable_prim.Is_int _ | T.Mutable_prim.Get_tag _
        | T.Mutable_prim.Make_block _ _ _ _
        | T.Mutable_prim.Block_load _ _ _ _ =>
          let! tmp1 := Flambda_primitive.free_names original_prim in
          Name_occurrences.fold_names tmp1 t
            (fun t dst => add_dependency src dst t)
        | T.Mutable_prim.Block_set _ _ _ _ =>
          let! tmp1 := Flambda_primitive.free_names original_prim in
          add_name_occurrences tmp1 t
        end)
      t mutable_let_prims_rev
  in
  (* 334-341 *)
  let* t :=
    Code_id.Map.fold
      (fun src name_occurrences graph =>
        fold_name_occurrences name_occurrences graph
          (fun t dst => add_code_id_dependency src dst t)
          (fun t dst => add_code_id_to_code_id src dst t))
      code_ids t
  in
  (* Build the graph of dependencies between continuation parameters and
     arguments. *)
  (* 344-412 *)
  Continuation.Map.fold
    (fun k rewrite_ids t =>
      let! tmp1 := Continuation.equal return_continuation k in
      let! tmp2 := or_else tmp1 (Continuation.equal exn_continuation k) in
      if tmp2
      then
        Apply_cont_rewrite_id.Map.fold
          (fun _rewrite_id args t =>
            Numeric_types.Int.Map.fold
              (fun _ cont_arg t =>
                match cont_arg with
                | T.Cont_arg.Simple simple =>
                  let! tmp3 := Simple.free_names simple in
                  add_name_occurrences tmp3 t
                | T.Cont_arg.New_let_binding var prim_free_names =>
                  let! tmp3 :=
                    Name_occurrences.singleton_variable var Name_mode.normal
                  in
                  let! tmp4 := Name_occurrences.union prim_free_names tmp3 in
                  add_name_occurrences tmp4 t
                | T.Cont_arg.Function_result => ret t
                end)
              args t)
          rewrite_ids t
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
          (fun rewrite_id args t =>
            let* correct_number_of_arguments :=
              match_exn
                (fun _ => Numeric_types.Int.Map.max_binding args)
                Not_found
                (fun _ =>
                  let! tmp3 := Array.length params in
                  ret (tmp3 =? 0))
                (fun '(max_arg, _) =>
                  let! tmp3 := Array.length params in
                  ret (max_arg =? tmp3 - 1))
            in
            (if negb correct_number_of_arguments
             then
               fatal_errorf4
                 "Mismatched number of argument and params for %a at rewrite_id %a"
                 Continuation.print k Apply_cont_rewrite_id.print rewrite_id
             else ret tt) ;;
            Numeric_types.Int.Map.fold
              (fun i cont_arg t =>
                (* Note on the direction of the edge:

                   We later do a reachability analysis to compute the transitive
                   closure of the used variables.

                   Therefore an edge from src to dst means: if src is used, then
                   dst is also used.

                   Applied here, this means : if the param of a continuation is
                   used, then any argument provided for that param is also used.
                   The other way wouldn't make much sense. *)
                let* src :=
                  let! tmp3 := Array.get params i in
                  Name.var tmp3
                in
                match cont_arg with
                | T.Cont_arg.Simple simple =>
                  let! tmp3 := Simple.free_names simple in
                  Name_occurrences.fold_names tmp3 t
                    (fun t dst => add_dependency src dst t)
                | T.Cont_arg.New_let_binding var prim_free_names =>
                  let* t :=
                    let! tmp3 := Name.var var in
                    add_dependency src tmp3 t
                  in
                  Name_occurrences.fold_names prim_free_names t
                    (fun t dst =>
                      let! tmp3 := Name.var var in
                      add_dependency tmp3 dst t)
                | T.Cont_arg.Function_result => ret t
                end)
              args t)
          rewrite_ids t)
    apply_cont_args t.

(* 414-430 *)
Definition create (return_continuation exn_continuation : Continuation.t)
    (code_age_relation : Flambda2_types.Code_age_relation.t)
    (used_value_slots : Or_unknown.t Name_occurrences.t)
    (code_ids_to_never_delete : Code_id.Set_.t)
    (map : Continuation.Map.t T.Continuation_info.t)
    : M Data_flow_graph.t :=
  (* Build the dependencies using the regular params and args of continuations,
     and the let-bindings in continuations handlers. *)
  let& is_toplevel :=
    match used_value_slots with
    | Or_unknown.Known _ => true
    | Or_unknown.Unknown => false
    end
  in
  (* 423-429: [add_continuation_info map ~return_continuation
     ~exn_continuation ~used_value_slots] is the function of the arguments
     that are left. *)
  let* t :=
    let! tmp1 := empty code_age_relation is_toplevel code_ids_to_never_delete in
    Continuation.Map.fold
      (fun k elt t =>
        add_continuation_info map return_continuation exn_continuation
          used_value_slots k elt t)
      map tmp1
  in
  ret t.

(* 432-451. The compiler's parameter is the pattern of all the fields,
   [as t]. *)
Definition required_names (t : Data_flow_graph.t) : M T.Data_flow_result.t :=
  let* '{| Data_flow_graph.code_age_relation := _;
           Data_flow_graph.name_to_name := _;
           Data_flow_graph.name_to_code_id := _;
           Data_flow_graph.code_id_to_name := _;
           Data_flow_graph.code_id_to_code_id := _;
           Data_flow_graph.unconditionally_used := unconditionally_used;
           Data_flow_graph.code_id_unconditionally_used :=
             code_id_unconditionally_used;
           Data_flow_graph.is_toplevel := is_toplevel
        |} :=
    ret t
  in
  let* name_queue := Queue.create tt in
  Name.Set_.iter (fun v => Queue.push v name_queue) unconditionally_used ;;
  let* code_id_queue := Queue.create tt in
  (if is_toplevel
   then
     Code_id.Set_.iter
       (fun v => Queue.push v code_id_queue)
       code_id_unconditionally_used
   else ret tt) ;;
  let_fuel! fuel in
  Reachable.reachable_names fuel t code_id_queue code_id_unconditionally_used
    Code_id.Set_.empty name_queue unconditionally_used.
