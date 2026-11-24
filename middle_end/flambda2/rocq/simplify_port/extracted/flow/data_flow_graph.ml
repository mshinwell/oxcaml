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
   middle_end/flambda2/rocq/simplify_port/flow/Data_flow_graph.v, which follows
   middle_end/flambda2/simplify/flow/data_flow_graph.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

open Port_monad
module T = Flow_types

type t =
  { code_age_relation : Flambda2_types.Code_age_relation.t;
    name_to_name : Name.Set.t Name.Map.t;
    name_to_code_id : Code_id.Set.t Name.Map.t;
    code_id_to_name : Name.Set.t Code_id.Map.t;
    code_id_to_code_id : Code_id.Set.t Code_id.Map.t;
    unconditionally_used : Name.Set.t;
    code_id_unconditionally_used : Code_id.Set.t;
    is_toplevel : bool
  }

(** val code_age_relation : t -> Flambda2_types.Code_age_relation.t **)

let code_age_relation t0 = t0.code_age_relation

(** val name_to_name : t -> Name.Set.t Name.Map.t **)

let name_to_name t0 = t0.name_to_name

(** val name_to_code_id : t -> Code_id.Set.t Name.Map.t **)

let name_to_code_id t0 = t0.name_to_code_id

(** val code_id_to_name : t -> Name.Set.t Code_id.Map.t **)

let code_id_to_name t0 = t0.code_id_to_name

(** val code_id_to_code_id : t -> Code_id.Set.t Code_id.Map.t **)

let code_id_to_code_id t0 = t0.code_id_to_code_id

(** val unconditionally_used : t -> Name.Set.t **)

let unconditionally_used t0 = t0.unconditionally_used

(** val code_id_unconditionally_used : t -> Code_id.Set.t **)

let code_id_unconditionally_used t0 = t0.code_id_unconditionally_used

(** val is_toplevel : t -> bool **)

let is_toplevel t0 = t0.is_toplevel

module Reachable = struct
  module Edge = struct
    (** val push : ('a1 -> 'a4 -> 'a3 coq_M) -> 'a3 -> ('a3 -> 'a3 -> 'a3 coq_M)
        -> (('a2 -> unit coq_M) -> 'a3 -> unit coq_M) -> ('a3 -> 'a3 -> 'a3
        coq_M) -> 'a1 -> 'a3 -> 'a2 Queue.t -> 'a4 -> 'a3 coq_M **)

    let push src_map_find dst_set_empty dst_set_diff dst_set_iter dst_set_union
        src enqueued queue graph =
      let neighbours =
        Port_monad.match_exn
          (fun _ -> src_map_find src graph)
          Port_monad.not_found
          (fun _ -> dst_set_empty)
          (fun set -> set)
      in
      let new_neighbours = dst_set_diff neighbours enqueued in
      let () = dst_set_iter (fun dst -> Queue.push dst queue) new_neighbours in
      dst_set_union enqueued new_neighbours
  end

  module Name_Name_Edge = struct
    (** val push : Name.t -> Name.Set.t -> Name.t Queue.t -> Name.Set.t
        Name.Map.t -> Name.Set.t coq_M **)

    let push src enqueued queue graph =
      Edge.push Name.Map.find Name.Set.empty Name.Set.diff Name.Set.iter
        Name.Set.union src enqueued queue graph
  end

  module Name_Code_id_Edge = struct
    (** val push : Name.t -> Code_id.Set.t -> Code_id.t Queue.t -> Code_id.Set.t
        Name.Map.t -> Code_id.Set.t coq_M **)

    let push src enqueued queue graph =
      Edge.push Name.Map.find Code_id.Set.empty Code_id.Set.diff
        Code_id.Set.iter Code_id.Set.union src enqueued queue graph
  end

  module Code_id_Name_Edge = struct
    (** val push : Code_id.t -> Name.Set.t -> Name.t Queue.t -> Name.Set.t
        Code_id.Map.t -> Name.Set.t coq_M **)

    let push src enqueued queue graph =
      Edge.push Code_id.Map.find Name.Set.empty Name.Set.diff Name.Set.iter
        Name.Set.union src enqueued queue graph
  end

  module Code_id_Code_id_Edge = struct
    (** val push : Code_id.t -> Code_id.Set.t -> Code_id.t Queue.t ->
        Code_id.Set.t Code_id.Map.t -> Code_id.Set.t coq_M **)

    let push src enqueued queue graph =
      Edge.push Code_id.Map.find Code_id.Set.empty Code_id.Set.diff
        Code_id.Set.iter Code_id.Set.union src enqueued queue graph
  end

  (** val reachable_names : t -> Code_id.t Queue.t -> Code_id.Set.t ->
      Code_id.Set.t -> Name.t Queue.t -> Name.Set.t -> T.Data_flow_result.t
      coq_M **)

  let rec reachable_names t0 code_id_queue code_id_enqueued older_enqueued
      name_queue name_enqueued =
    Port_monad.match_exn
      (fun _ -> Queue.take name_queue)
      ((fun () -> Queue.Empty), function Queue.Empty -> Some () | _ -> None)
      (fun _ ->
        if t0.is_toplevel
        then
          if Queue.is_empty code_id_queue
          then
            { T.Data_flow_result.required_names = name_enqueued;
              T.Data_flow_result.reachable_code_ids =
                Or_unknown.Known
                  { T.Reachable_code_ids.live_code_ids = code_id_enqueued;
                    T.Reachable_code_ids.ancestors_of_live_code_ids =
                      older_enqueued
                  }
            }
          else
            reachable_code_ids t0 code_id_queue code_id_enqueued
              (Queue.create ()) older_enqueued name_queue name_enqueued
        else
          { T.Data_flow_result.required_names = name_enqueued;
            T.Data_flow_result.reachable_code_ids = Or_unknown.Unknown
          })
      (fun src ->
        let name_enqueued0 =
          Name_Name_Edge.push src name_enqueued name_queue t0.name_to_name
        in
        let code_id_enqueued0 =
          Name_Code_id_Edge.push src code_id_enqueued code_id_queue
            t0.name_to_code_id
        in
        reachable_names t0 code_id_queue code_id_enqueued0 older_enqueued
          name_queue name_enqueued0)

  (** val reachable_code_ids : t -> Code_id.t Queue.t -> Code_id.Set.t ->
      Code_id.t Queue.t -> Code_id.Set.t -> Name.t Queue.t -> Name.Set.t ->
      T.Data_flow_result.t coq_M **)

  and reachable_code_ids t0 code_id_queue code_id_enqueued older_queue
      older_enqueued name_queue name_enqueued =
    Port_monad.match_exn
      (fun _ -> Queue.take code_id_queue)
      ((fun () -> Queue.Empty), function Queue.Empty -> Some () | _ -> None)
      (fun _ ->
        if Queue.is_empty older_queue
        then
          reachable_names t0 code_id_queue code_id_enqueued older_enqueued
            name_queue name_enqueued
        else
          reachable_older_code_ids t0 code_id_queue code_id_enqueued older_queue
            older_enqueued name_queue name_enqueued)
      (fun src ->
        let name_enqueued0 =
          Code_id_Name_Edge.push src name_enqueued name_queue t0.code_id_to_name
        in
        let code_id_enqueued0 =
          Code_id_Code_id_Edge.push src code_id_enqueued code_id_queue
            t0.code_id_to_code_id
        in
        let older_enqueued0 =
          if Code_id.Set.mem src older_enqueued
          then older_enqueued
          else
            let () = Queue.push src older_queue in
            Code_id.Set.add src older_enqueued
        in
        reachable_code_ids t0 code_id_queue code_id_enqueued0 older_queue
          older_enqueued0 name_queue name_enqueued0)

  (** val reachable_older_code_ids : t -> Code_id.t Queue.t -> Code_id.Set.t ->
      Code_id.t Queue.t -> Code_id.Set.t -> Name.t Queue.t -> Name.Set.t ->
      T.Data_flow_result.t coq_M **)

  and reachable_older_code_ids t0 code_id_queue code_id_enqueued older_queue
      older_enqueued name_queue name_enqueued =
    Port_monad.match_exn
      (fun _ -> Queue.take older_queue)
      ((fun () -> Queue.Empty), function Queue.Empty -> Some () | _ -> None)
      (fun _ ->
        reachable_code_ids t0 code_id_queue code_id_enqueued older_queue
          older_enqueued name_queue name_enqueued)
      (fun src ->
        match
          Flambda2_types.Code_age_relation.get_older_version_of
            t0.code_age_relation src
        with
        | Some dst ->
          if Code_id.Set.mem dst older_enqueued
          then
            if Code_id.Set.mem dst code_id_enqueued
            then
              reachable_older_code_ids t0 code_id_queue code_id_enqueued
                older_queue older_enqueued name_queue name_enqueued
            else
              let code_id_enqueued0 = Code_id.Set.add dst code_id_enqueued in
              let () = Queue.push dst code_id_queue in
              reachable_older_code_ids t0 code_id_queue code_id_enqueued0
                older_queue older_enqueued name_queue name_enqueued
          else
            let older_enqueued0 = Code_id.Set.add dst older_enqueued in
            let () = Queue.push dst older_queue in
            reachable_older_code_ids t0 code_id_queue code_id_enqueued
              older_queue older_enqueued0 name_queue name_enqueued
        | None ->
          reachable_older_code_ids t0 code_id_queue code_id_enqueued older_queue
            older_enqueued name_queue name_enqueued)
end

(** val empty : Flambda2_types.Code_age_relation.t -> bool -> Code_id.Set.t -> t
    coq_M **)

let empty code_age_relation0 is_toplevel0 code_ids_to_never_delete =
  { code_age_relation = code_age_relation0;
    name_to_name = Name.Map.empty;
    name_to_code_id = Name.Map.empty;
    code_id_to_name = Code_id.Map.empty;
    code_id_to_code_id = Code_id.Map.empty;
    unconditionally_used = Name.Set.empty;
    code_id_unconditionally_used = code_ids_to_never_delete;
    is_toplevel = is_toplevel0
  }

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  let { code_age_relation = code_age_relation0;
        name_to_name = name_to_name0;
        name_to_code_id = name_to_code_id0;
        code_id_to_name = code_id_to_name0;
        code_id_to_code_id = code_id_to_code_id0;
        unconditionally_used = unconditionally_used0;
        code_id_unconditionally_used = code_id_unconditionally_used0;
        is_toplevel = is_toplevel0
      } =
    t0
  in
  Format.fprintf ppf
    "@[<hov 1>(@[<hov 1>(is_toplevel %b)@]@ @[<hov 1>(code_age_relation@ \
     %a)@]@ @[<hov 1>(name_to_name@ %a)@]@ @[<hov 1>(name_to_code_id@ %a)@]@ \
     @[<hov 1>(code_id_to_name@ %a)@]@ @[<hov 1>(code_id_to_code_id@ %a)@]@ \
     @[<hov 1>(unconditionally_used@ %a)@]@ @[<hov \
     1>(code_id_unconditionally_used@ %a)@])@]"
    is_toplevel0 Flambda2_types.Code_age_relation.print code_age_relation0
    (Name.Map.print Name.Set.print)
    name_to_name0
    (Name.Map.print Code_id.Set.print)
    name_to_code_id0
    (Code_id.Map.print Name.Set.print)
    code_id_to_name0
    (Code_id.Map.print Code_id.Set.print)
    code_id_to_code_id0 Name.Set.print unconditionally_used0 Code_id.Set.print
    code_id_unconditionally_used0

(** val fold_name_occurrences : Name_occurrences.t -> 'a1 -> ('a1 -> Name.t ->
    'a1 coq_M) -> ('a1 -> Code_id.Set.t -> 'a1 coq_M) -> 'a1 coq_M **)

let fold_name_occurrences name_occurrences init names code_ids0 =
  Name_occurrences.fold_names name_occurrences
    (code_ids0 init (Name_occurrences.code_ids name_occurrences))
    names

(** val add_code_id_dep : Name.t -> Code_id.Set.t -> t -> t coq_M **)

let add_code_id_dep src dst t0 =
  let { code_age_relation = _;
        name_to_name = _;
        name_to_code_id = name_to_code_id0;
        code_id_to_name = _;
        code_id_to_code_id = _;
        unconditionally_used = _;
        code_id_unconditionally_used = _;
        is_toplevel = _
      } =
    t0
  in
  let name_to_code_id1 =
    Name.Map.update src
      (fun x ->
        match x with
        | Some old ->
          Misc.fatal_errorf "Same name bound multiple times: %a -> %a, %a"
            Name.print src Code_id.Set.print old Code_id.Set.print dst
        | None -> if Code_id.Set.is_empty dst then None else Some dst)
      name_to_code_id0
  in
  (fun t x__1 -> { t with name_to_code_id = x__1 }) t0 name_to_code_id1

(** val add_dependency : Name.t -> Name.t -> t -> t coq_M **)

let add_dependency src dst t0 =
  let { code_age_relation = _;
        name_to_name = name_to_name0;
        name_to_code_id = _;
        code_id_to_name = _;
        code_id_to_code_id = _;
        unconditionally_used = _;
        code_id_unconditionally_used = _;
        is_toplevel = _
      } =
    t0
  in
  let name_to_name1 =
    Name.Map.update src
      (fun x ->
        match x with
        | Some set -> Some (Name.Set.add dst set)
        | None -> Some (Name.Set.singleton dst))
      name_to_name0
  in
  (fun t x__1 -> { t with name_to_name = x__1 }) t0 name_to_name1

(** val add_code_id_dependency : Code_id.t -> Name.t -> t -> t coq_M **)

let add_code_id_dependency src dst t0 =
  let { code_age_relation = _;
        name_to_name = _;
        name_to_code_id = _;
        code_id_to_name = code_id_to_name0;
        code_id_to_code_id = _;
        unconditionally_used = _;
        code_id_unconditionally_used = _;
        is_toplevel = _
      } =
    t0
  in
  let code_id_to_name1 =
    Code_id.Map.update src
      (fun x ->
        match x with
        | Some set -> Some (Name.Set.add dst set)
        | None -> Some (Name.Set.singleton dst))
      code_id_to_name0
  in
  (fun t x__1 -> { t with code_id_to_name = x__1 }) t0 code_id_to_name1

(** val add_code_id_to_code_id : Code_id.t -> Code_id.Set.t -> t -> t coq_M **)

let add_code_id_to_code_id src dst t0 =
  let { code_age_relation = _;
        name_to_name = _;
        name_to_code_id = _;
        code_id_to_name = _;
        code_id_to_code_id = code_id_to_code_id0;
        unconditionally_used = _;
        code_id_unconditionally_used = _;
        is_toplevel = _
      } =
    t0
  in
  let code_id_to_code_id1 =
    Code_id.Map.update src
      (fun x ->
        match x with
        | Some old ->
          Misc.fatal_errorf "Same code_id bound multiple times: %a -> %a, %a"
            Code_id.print src Code_id.Set.print old Code_id.Set.print dst
        | None -> if Code_id.Set.is_empty dst then None else Some dst)
      code_id_to_code_id0
  in
  (fun t x__1 -> { t with code_id_to_code_id = x__1 }) t0 code_id_to_code_id1

(** val add_name_occurrences : Name_occurrences.t -> t -> t coq_M **)

let add_name_occurrences name_occurrences t0 =
  let { code_age_relation = _;
        name_to_name = _;
        name_to_code_id = _;
        code_id_to_name = _;
        code_id_to_code_id = _;
        unconditionally_used = unconditionally_used0;
        code_id_unconditionally_used = code_id_unconditionally_used0;
        is_toplevel = _
      } =
    t0
  in
  let unconditionally_used1 =
    Name_occurrences.fold_names name_occurrences unconditionally_used0
      (fun set name -> Name.Set.add name set)
  in
  let code_id_unconditionally_used1 =
    Code_id.Set.union
      (Name_occurrences.code_ids name_occurrences)
      code_id_unconditionally_used0
  in
  (fun t x__1 x__2 ->
    { t with unconditionally_used = x__1; code_id_unconditionally_used = x__2 })
    t0 unconditionally_used1 code_id_unconditionally_used1

(** val add_continuation_info : T.Continuation_info.t Continuation.Map.t ->
    Continuation.t -> Continuation.t -> Name_occurrences.t Or_unknown.t ->
    Continuation.t -> T.Continuation_info.t -> t -> t coq_M **)

let add_continuation_info map0 return_continuation exn_continuation
    used_value_slots _ elt t0 =
  let { T.Continuation_info.continuation = _;
        T.Continuation_info.recursive = _;
        T.Continuation_info.is_exn_handler = _;
        T.Continuation_info.params = _;
        T.Continuation_info.parent_continuation = _;
        T.Continuation_info.used_in_handler = used_in_handler0;
        T.Continuation_info.bindings = bindings0;
        T.Continuation_info.direct_aliases = direct_aliases0;
        T.Continuation_info.mutable_let_prims_rev = mutable_let_prims_rev0;
        T.Continuation_info.defined = _;
        T.Continuation_info.code_ids = code_ids0;
        T.Continuation_info.value_slots = value_slots0;
        T.Continuation_info.apply_cont_args = apply_cont_args0
      } =
    elt
  in
  let t1 = add_name_occurrences used_in_handler0 t0 in
  let is_value_slot_used =
    match used_value_slots with
    | Or_unknown.Known used_value_slots0 ->
      Name_occurrences.value_slot_is_used_or_imported used_value_slots0
    | Or_unknown.Unknown -> fun _ -> true
  in
  let t2 =
    Value_slot.Map.fold
      (fun value_slot map1 t2 ->
        if not (is_value_slot_used value_slot)
        then t2
        else
          Name.Map.fold
            (fun closure_name values_in_env t3 ->
              Name_occurrences.fold_names values_in_env t3
                (fun t4 value_in_env ->
                  add_dependency closure_name value_in_env t4))
            map1 t2)
      value_slots0 t1
  in
  let t3 =
    Name.Map.fold
      (fun src name_occurrences graph ->
        fold_name_occurrences name_occurrences graph
          (fun t3 dst -> add_dependency src dst t3)
          (fun t3 dst -> add_code_id_dep src dst t3))
      bindings0 t2
  in
  let t4 =
    Variable.Map.fold
      (fun src simple graph ->
        let src0 = Name.var src in
        let name_occurrences = Simple.free_names simple in
        fold_name_occurrences name_occurrences graph
          (fun t4 dst -> add_dependency src0 dst t4)
          (fun t4 dst -> add_code_id_dep src0 dst t4))
      direct_aliases0 t3
  in
  let t5 =
    List.fold_left
      (fun t5 pat ->
        let { T.Mutable_let_prim.bound_var = bound_var0;
              T.Mutable_let_prim.prim = prim0;
              T.Mutable_let_prim.original_prim = original_prim0;
              T.Mutable_let_prim.named_rewrite_id = _
            } =
          pat
        in
        let src = Name.var bound_var0 in
        (fun f__1 f__2 f__3 f__4 f__5 x__0 ->
          match (x__0 : Flow_types.Mutable_prim.t) with
          | Flow_types.Mutable_prim.Is_int x__1 -> f__1 x__1
          | Flow_types.Mutable_prim.Get_tag x__1 -> f__2 x__1
          | Flow_types.Mutable_prim.Block_load
              { bak = x__1; mut = x__2; block = x__3; field = x__4 } ->
            f__3 x__1 x__2 x__3 x__4
          | Flow_types.Mutable_prim.Block_set
              { bak = x__1; block = x__2; field = x__3; value = x__4 } ->
            f__4 x__1 x__2 x__3 x__4
          | Flow_types.Mutable_prim.Make_block
              { kind = x__1; mut = x__2; alloc_mode = x__3; fields = x__4 } ->
            f__5 x__1 x__2 x__3 x__4)
          (fun _ ->
            Name_occurrences.fold_names
              (Flambda_primitive.free_names original_prim0) t5 (fun t6 dst ->
                add_dependency src dst t6))
          (fun _ ->
            Name_occurrences.fold_names
              (Flambda_primitive.free_names original_prim0) t5 (fun t6 dst ->
                add_dependency src dst t6))
          (fun _ _ _ _ ->
            Name_occurrences.fold_names
              (Flambda_primitive.free_names original_prim0) t5 (fun t6 dst ->
                add_dependency src dst t6))
          (fun _ _ _ _ ->
            add_name_occurrences
              (Flambda_primitive.free_names original_prim0)
              t5)
          (fun _ _ _ _ ->
            Name_occurrences.fold_names
              (Flambda_primitive.free_names original_prim0) t5 (fun t6 dst ->
                add_dependency src dst t6))
          prim0)
      t4 mutable_let_prims_rev0
  in
  let t6 =
    Code_id.Map.fold
      (fun src name_occurrences graph ->
        fold_name_occurrences name_occurrences graph
          (fun t6 dst -> add_code_id_dependency src dst t6)
          (fun t6 dst -> add_code_id_to_code_id src dst t6))
      code_ids0 t5
  in
  Continuation.Map.fold
    (fun k rewrite_ids t7 ->
      if
        Continuation.equal return_continuation k
        || Continuation.equal exn_continuation k
      then
        Apply_cont_rewrite_id.Map.fold
          (fun _ args t8 ->
            Numeric_types.Int.Map.fold
              (fun _ cont_arg t9 ->
                match cont_arg with
                | Flow_types.Cont_arg.Function_result -> t9
                | Flow_types.Cont_arg.Simple simple ->
                  add_name_occurrences (Simple.free_names simple) t9
                | Flow_types.Cont_arg.New_let_binding (var, prim_free_names) ->
                  add_name_occurrences
                    (Name_occurrences.union prim_free_names
                       (Name_occurrences.singleton_variable var Name_mode.normal))
                    t9)
              args t8)
          rewrite_ids t7
      else
        let params0 =
          Port_monad.match_exn
            (fun _ -> Continuation.Map.find k map0)
            Port_monad.not_found
            (fun _ ->
              Misc.fatal_errorf "Continuation not found during Data_flow: %a@."
                Continuation.print k)
            (fun elt0 ->
              Array.of_list
                (Bound_parameters.vars elt0.Flow_types.Continuation_info.params))
        in
        Apply_cont_rewrite_id.Map.fold
          (fun rewrite_id args t8 ->
            let correct_number_of_arguments =
              Port_monad.match_exn
                (fun _ -> Numeric_types.Int.Map.max_binding args)
                Port_monad.not_found
                (fun _ -> Array.length params0 = 0)
                (fun pat ->
                  let max_arg, _ = pat in
                  max_arg = Array.length params0 - 1)
            in
            let () =
              if not correct_number_of_arguments
              then
                Misc.fatal_errorf
                  "Mismatched number of argument and params for %a at \
                   rewrite_id %a"
                  Continuation.print k Apply_cont_rewrite_id.print rewrite_id
              else ()
            in
            Numeric_types.Int.Map.fold
              (fun i cont_arg t9 ->
                let src = Name.var (Array.get params0 i) in
                match cont_arg with
                | Flow_types.Cont_arg.Function_result -> t9
                | Flow_types.Cont_arg.Simple simple ->
                  Name_occurrences.fold_names (Simple.free_names simple) t9
                    (fun t10 dst -> add_dependency src dst t10)
                | Flow_types.Cont_arg.New_let_binding (var, prim_free_names) ->
                  let t10 = add_dependency src (Name.var var) t9 in
                  Name_occurrences.fold_names prim_free_names t10
                    (fun t11 dst -> add_dependency (Name.var var) dst t11))
              args t8)
          rewrite_ids t7)
    apply_cont_args0 t6

(** val create : Continuation.t -> Continuation.t ->
    Flambda2_types.Code_age_relation.t -> Name_occurrences.t Or_unknown.t ->
    Code_id.Set.t -> T.Continuation_info.t Continuation.Map.t -> t coq_M **)

let create return_continuation exn_continuation code_age_relation0
    used_value_slots code_ids_to_never_delete map0 =
  let is_toplevel0 =
    match used_value_slots with
    | Or_unknown.Known _ -> true
    | Or_unknown.Unknown -> false
  in
  let t0 =
    Continuation.Map.fold
      (fun k elt t0 ->
        add_continuation_info map0 return_continuation exn_continuation
          used_value_slots k elt t0)
      map0
      (empty code_age_relation0 is_toplevel0 code_ids_to_never_delete)
  in
  t0

(** val required_names : t -> T.Data_flow_result.t coq_M **)

let required_names t0 =
  let { code_age_relation = _;
        name_to_name = _;
        name_to_code_id = _;
        code_id_to_name = _;
        code_id_to_code_id = _;
        unconditionally_used = unconditionally_used0;
        code_id_unconditionally_used = code_id_unconditionally_used0;
        is_toplevel = is_toplevel0
      } =
    t0
  in
  let name_queue = Queue.create () in
  let () =
    Name.Set.iter (fun v -> Queue.push v name_queue) unconditionally_used0
  in
  let code_id_queue = Queue.create () in
  let () =
    if is_toplevel0
    then
      Code_id.Set.iter
        (fun v -> Queue.push v code_id_queue)
        code_id_unconditionally_used0
    else ()
  in
  Reachable.reachable_names t0 code_id_queue code_id_unconditionally_used0
    Code_id.Set.empty name_queue unconditionally_used0
