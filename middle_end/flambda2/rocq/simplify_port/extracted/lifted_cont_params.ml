(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                        Guillaume Bury, OCamlPro                        *)
(*                                                                        *)
(*   Copyright 2023--2024 OCamlPro SAS                                    *)
(*   Copyright 2023--2024 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* Extracted by Rocq from
   middle_end/flambda2/rocq/simplify_port/Lifted_cont_params.v, which follows
   middle_end/flambda2/simplify/lifted_cont_params.ml function by function. Do
   not edit this file: change the .v file and run make in
   middle_end/flambda2/rocq/simplify_port. *)

module BP = Bound_parameter
open Port_abbreviations
open Port_monad

type t =
  { len : int;
    new_params_indexed : BP.t BP.Map.t
  }

(** val len : t -> int **)

let len t0 = t0.len

(** val new_params_indexed : t -> BP.t BP.Map.t **)

let new_params_indexed t0 = t0.new_params_indexed

(** val print : Format.formatter -> t -> unit coq_M **)

let print ppf t0 =
  let { len = _; new_params_indexed = new_params_indexed0 } = t0 in
  Format.fprintf ppf "@[<hov 1>(@[<hov 1>(new_params_indexed@ %a)@])@]"
    (BP.Map.print BP.print) new_params_indexed0

(** val empty : t **)

let empty = { len = 0; new_params_indexed = BP.Map.empty }

(** val is_empty : t -> bool coq_M **)

let is_empty t0 =
  let { len = len0; new_params_indexed = _ } = t0 in
  len0 = 0

(** val length : t -> int coq_M **)

let length t0 = t0.len

(** val new_param : t -> Replay_history.t -> BP.t -> t coq_M **)

let new_param t0 replay_history bound_param =
  let key =
    match Replay_history.replay_variable_mapping replay_history with
    | Still_recording -> bound_param
    | Replayed variable_mapping ->
      let param_var, param_duid = BP.var_and_uid bound_param in
      let original_var = Variable.Map.find param_var variable_mapping in
      BP.create original_var (BP.kind bound_param) param_duid
  in
  let new_params_indexed0 = BP.Map.add key bound_param t0.new_params_indexed in
  { len = t0.len + 1; new_params_indexed = new_params_indexed0 }

(** val rename : t -> (t * Renaming.t) coq_M **)

let rename t0 =
  let bindings = BP.Map.bindings t0.new_params_indexed in
  let keys, bound_param_list = List.split bindings in
  let bound_params = Bound_parameters.create bound_param_list in
  let new_bound_params = Bound_parameters.rename bound_params in
  let renaming = Bound_parameters.renaming bound_params new_bound_params in
  let new_params_indexed0 =
    BP.Map.of_list
      (List.combine keys (Bound_parameters.to_list new_bound_params))
  in
  ( (fun t new_params_indexed -> { t with new_params_indexed })
      t0 new_params_indexed0,
    renaming )

(** val fold_aux : 'a1 -> (BP.t -> BP.t -> 'a1 -> 'a1 coq_M) -> t -> 'a1 coq_M **)

let fold_aux init f t0 =
  let { len = _; new_params_indexed = new_params_indexed0 } = t0 in
  BP.Map.fold f new_params_indexed0 init

(** val fold : 'a1 -> (BP.t -> 'a1 -> 'a1 coq_M) -> t -> 'a1 coq_M **)

let fold init f t0 = fold_aux init (fun _ -> f) t0

(** val find_arg : BP.t -> t list -> Simple.t coq_M **)

let rec find_arg bp = function
  | [] ->
    Misc.fatal_errorf
      "Missing lifted param id: %a not found in lifted_cont_params stack"
      BP.print bp
  | t0 :: r -> (
    let { len = _; new_params_indexed = new_params_indexed0 } = t0 in
    match BP.Map.find_opt bp new_params_indexed0 with
    | Some param -> BP.simple param
    | None -> find_arg bp r)

(** val args : t -> t list -> Simple.t list coq_M **)

let args callee_lifted_params caller_stack_lifted_params =
  fold_aux []
    (fun bp_key _ acc -> find_arg bp_key caller_stack_lifted_params :: acc)
    callee_lifted_params

(** val bound_parameters : t -> Bound_parameters.t coq_M **)

let bound_parameters t0 =
  Bound_parameters.create
    (fold [] (fun bound_param acc -> bound_param :: acc) t0)
