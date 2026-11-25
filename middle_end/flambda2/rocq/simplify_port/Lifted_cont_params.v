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

(* This file follows middle_end/flambda2/simplify/lifted_cont_params.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the arguments by place) is that of
   GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Bound_parameter Bound_parameters Format List
  Renaming Replay_history Simple Variable_.
(* CONSTRUCTORS-WITHOUT-MODULE: Replay_history.replay_result *)
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* 16 *)
From SimplifyPort.abbrev.lifted_cont_params Require Import Port_abbreviations.
(*OCAML
module BP = Bound_parameter
OCAML*)

(* 18-21 *)
Record t : Type :=
  { len : int;
    new_params_indexed : BP.Map.t BP.t
  }.

(* 23-25 *)
(* PORT-GAP(loose): the record pattern of the parameter is a match, here and
   at [is_empty], [length] and [fold_aux]. *)
Definition print (ppf : Format.formatter) (t : Lifted_cont_params.t) : M unit :=
  match t with
  | {| len := _; new_params_indexed := new_params_indexed |} =>
    let! tmp1 := papp1 BP.Map.print BP.print in
    Format.fprintf2 ppf "@[<hov 1>(@[<hov 1>(new_params_indexed@ %a)@])@]"
      tmp1 new_params_indexed
  end.

(* 27 *)
Definition empty : t := {| len := 0; new_params_indexed := BP.Map.empty |}.

(* 29 *)
Definition is_empty (t : Lifted_cont_params.t) : M bool :=
  match t with
  | {| len := len; new_params_indexed := _ |} => ret (len =? 0)
  end.

(* 31 *)
Definition length (t : Lifted_cont_params.t) : M int :=
  match t with
  | {| len := len; new_params_indexed := _ |} => ret len
  end.

(* 33-43 *)
Definition new_param (t : Lifted_cont_params.t)
    (replay_history : Replay_history.t) (bound_param : BP.t)
    : M Lifted_cont_params.t :=
  let* key :=
    let! tmp1 := Replay_history.replay_variable_mapping replay_history in
    match tmp1 with
    | Replay_history.Still_recording => ret bound_param
    | Replay_history.Replayed variable_mapping =>
      let* '(param_var, param_duid) := BP.var_and_uid bound_param in
      let* original_var := Variable_.Map.find param_var variable_mapping in
      let! tmp1 := BP.kind bound_param in
      BP.create original_var tmp1 param_duid
    end
  in
  let* new_params_indexed :=
    BP.Map.add key bound_param t.(new_params_indexed)
  in
  ret {| len := t.(len) + 1; new_params_indexed := new_params_indexed |}.

(* 57. [{ t with new_params_indexed }]. *)
Definition update_new_params_indexed (t : Lifted_cont_params.t)
    (new_params_indexed : BP.Map.t BP.t) : Lifted_cont_params.t :=
  {| len := t.(len);
     new_params_indexed := new_params_indexed
  |}.
Extract Inlined Constant update_new_params_indexed =>
  "(fun t new_params_indexed -> { t with new_params_indexed =
   new_params_indexed })".

(* 45-57 *)
Definition rename (t : Lifted_cont_params.t)
    : M (Lifted_cont_params.t * Renaming.t) :=
  let* bindings := BP.Map.bindings t.(new_params_indexed) in
  let* '(keys, bound_param_list) := List.split bindings in
  let* bound_params := Bound_parameters.create bound_param_list in
  let* new_bound_params := Bound_parameters.rename bound_params in
  let* renaming := Bound_parameters.renaming bound_params new_bound_params in
  let* new_params_indexed :=
    let! tmp1 := Bound_parameters.to_list new_bound_params in
    let! tmp2 := List.combine keys tmp1 in
    BP.Map.of_list tmp2
  in
  ret (update_new_params_indexed t new_params_indexed, renaming).

(* 59-60 *)
Definition fold_aux {A : Type} (init : A) (f : BP.t -> BP.t -> A -> M A)
    (t : Lifted_cont_params.t) : M A :=
  match t with
  | {| len := _; new_params_indexed := new_params_indexed |} =>
    BP.Map.fold f new_params_indexed init
  end.

(* 62 *)
Definition fold {A : Type} (init : A) (f : BP.t -> A -> M A)
    (t : Lifted_cont_params.t) : M A :=
  fold_aux init (fun _ param acc => f param acc) t.

(* 64-72. The recursion is on the list. *)
Fixpoint find_arg (bp : BP.t) (l : list Lifted_cont_params.t) : M Simple.t :=
  match l with
  | [] =>
    fatal_errorf2
      "Missing lifted param id: %a not found in lifted_cont_params stack"
      BP.print bp
  | {| len := _; new_params_indexed := new_params_indexed |} :: r =>
    let! tmp1 := BP.Map.find_opt bp new_params_indexed in
    match tmp1 with
    | Some param => BP.simple param
    | None => find_arg bp r
    end
  end.

(* NOTE about the order of the returned args/params for the {args} and
   {bound_parameters} functions: The exact order does not matter as long as both
   functions return params (or their corresponding arguments) **in the same
   order**.

   The current implementations return the parameters/arguments in the reverse
   order of the bindings in the Map, but that's fine since it is the case for
   both functions. *)
(* 82-84. In the compiler: [fold_aux callee_lifted_params ~init:[] ~f]. *)
Definition args (callee_lifted_params : Lifted_cont_params.t)
    (caller_stack_lifted_params : list Lifted_cont_params.t)
    : M (list Simple.t) :=
  fold_aux []
    (fun bp_key _callee_param acc =>
      let! tmp1 := find_arg bp_key caller_stack_lifted_params in
      ret (tmp1 :: acc))
    callee_lifted_params.

(* 86-88. In the compiler: [fold t ~init:[] ~f]. *)
Definition bound_parameters (t : Lifted_cont_params.t) : M Bound_parameters.t :=
  let! tmp1 := fold [] (fun bound_param acc => ret (bound_param :: acc)) t in
  Bound_parameters.create tmp1.
