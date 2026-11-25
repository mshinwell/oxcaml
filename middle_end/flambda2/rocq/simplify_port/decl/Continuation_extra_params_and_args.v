(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                       Pierre Chambart, OCamlPro                        *)
(*           Mark Shinwell and Leo White, Jane Street Europe              *)
(*                                                                        *)
(*   Copyright 2013--2019 OCamlPro SAS                                    *)
(*   Copyright 2014--2019 Jane Street Group LLC                           *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

(* GENERATED, not written by hand: the declarations of what the port of
   Simplify uses of the compiler's module [Continuation_extra_params_and_args], after its interface
   middle_end/flambda2/simplify/continuation_extra_params_and_args.mli
   (Git blob 26e254eeca3281320c3558670becbbffd9e1ada9). Made by tools/declgen
   (see decl/README.md): a change is made there, not here. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Bound_parameter Bound_parameters Flambda_primitive Format Or_invalid Simple Variable_.

Module Extra_arg.
  (* continuation_extra_params_and_args.mli:18  type t = | Already_in_scope of Simple.t | New_let_binding of Variable.t * Flambda_primitive.t | New_let_binding_with_named_args of Variable.t * (Simple.t list -> Flambda_primitive.t) *)
  Inductive t : Type :=
  | Already_in_scope : Simple.t -> t
  | New_let_binding : Variable_.t -> Flambda_primitive.t -> t
  | New_let_binding_with_named_args : Variable_.t -> (list Simple.t -> M Flambda_primitive.t) -> t.
  Extract Inductive t => "Continuation_extra_params_and_args.Extra_arg.t" [ "Continuation_extra_params_and_args.Extra_arg.Already_in_scope" "Continuation_extra_params_and_args.Extra_arg.New_let_binding" "Continuation_extra_params_and_args.Extra_arg.New_let_binding_with_named_args" ].
  (* continuation_extra_params_and_args.mli:24  val print : Format.formatter -> t -> unit *)
  Parameter print : Format.formatter -> t -> M unit.
  Extract Inlined Constant print => "Continuation_extra_params_and_args.Extra_arg.print".
  Module List.
    (* continuation_extra_params_and_args.mli:27  type nonrec t = t list *)
    Definition t : Type := list Continuation_extra_params_and_args.Extra_arg.t.
    Extract Inlined Constant t => "Continuation_extra_params_and_args.Extra_arg.List.t".
    (* continuation_extra_params_and_args.mli:29  val print : Format.formatter -> t -> unit *)
    Parameter print : Format.formatter -> t -> M unit.
    Extract Inlined Constant print => "Continuation_extra_params_and_args.Extra_arg.List.print".
  End List.
End Extra_arg.
(* continuation_extra_params_and_args.mli:33  type t = private | Empty | Non_empty of { extra_params : Bound_parameters.t; extra_args : Extra_arg.t list Or_invalid.t Apply_cont_rewrite_id.Map.t } *)
Inductive t : Type :=
| Empty : t
| Non_empty : Bound_parameters.t -> Apply_cont_rewrite_id.Map.t (Or_invalid.t (list Continuation_extra_params_and_args.Extra_arg.t)) -> t.
Extract Inductive t => "Continuation_extra_params_and_args.t" [ "Continuation_extra_params_and_args.Empty" "(fun (x__1, x__2) -> (Continuation_extra_params_and_args.Non_empty { extra_params = x__1; extra_args = x__2 } : Continuation_extra_params_and_args.t))" ] "(fun f__1 f__2 x__0 -> match (x__0 : Continuation_extra_params_and_args.t) with Continuation_extra_params_and_args.Empty -> f__1 () | Continuation_extra_params_and_args.Non_empty { extra_params = x__1; extra_args = x__2 } -> f__2 x__1 x__2)".
(* continuation_extra_params_and_args.mli:40  val print : Format.formatter -> t -> unit *)
Parameter print : Format.formatter -> t -> M unit.
Extract Inlined Constant print => "Continuation_extra_params_and_args.print".
(* continuation_extra_params_and_args.mli:42  val is_empty : t -> bool *)
Parameter is_empty : t -> M bool.
Extract Inlined Constant is_empty => "Continuation_extra_params_and_args.is_empty".
(* continuation_extra_params_and_args.mli:48  val empty : t *)
Parameter empty : t.
Extract Inlined Constant empty => "Continuation_extra_params_and_args.empty".
(* continuation_extra_params_and_args.mli:50  val add : t -> invalids:Apply_cont_rewrite_id.Set.t -> extra_param:Bound_parameter.t -> extra_args:Extra_arg.t Apply_cont_rewrite_id.Map.t -> t *)
Parameter add : t -> Apply_cont_rewrite_id.Set_.t -> Bound_parameter.t -> Apply_cont_rewrite_id.Map.t Continuation_extra_params_and_args.Extra_arg.t -> M t.
Extract Inlined Constant add => "Continuation_extra_params_and_args.add".
(* continuation_extra_params_and_args.mli:59  val init_with_params_only : Bound_parameters.t -> t *)
Parameter init_with_params_only : Bound_parameters.t -> M t.
Extract Inlined Constant init_with_params_only => "Continuation_extra_params_and_args.init_with_params_only".
(* continuation_extra_params_and_args.mli:61  val add_args_for_all_params : t -> Apply_cont_rewrite_id.t -> Extra_arg.t list -> t *)
Parameter add_args_for_all_params : t -> Apply_cont_rewrite_id.t -> list Continuation_extra_params_and_args.Extra_arg.t -> M t.
Extract Inlined Constant add_args_for_all_params => "Continuation_extra_params_and_args.add_args_for_all_params".
(* continuation_extra_params_and_args.mli:66  val concat : outer:t -> inner:t -> t *)
Parameter concat : t -> t -> M t.
Extract Inlined Constant concat => "Continuation_extra_params_and_args.concat".
(* continuation_extra_params_and_args.mli:68  val replace_extra_args : t -> Extra_arg.t list Or_invalid.t Apply_cont_rewrite_id.Map.t -> t *)
Parameter replace_extra_args : t -> Apply_cont_rewrite_id.Map.t (Or_invalid.t (list Continuation_extra_params_and_args.Extra_arg.t)) -> M t.
Extract Inlined Constant replace_extra_args => "Continuation_extra_params_and_args.replace_extra_args".
(* continuation_extra_params_and_args.mli:71  val extra_params : t -> Bound_parameters.t *)
Parameter extra_params : t -> M Bound_parameters.t.
Extract Inlined Constant extra_params => "Continuation_extra_params_and_args.extra_params".
(* continuation_extra_params_and_args.mli:73  val extra_args : t -> Extra_arg.t list Or_invalid.t Apply_cont_rewrite_id.Map.t *)
Parameter extra_args : t -> M (Apply_cont_rewrite_id.Map.t (Or_invalid.t (list Continuation_extra_params_and_args.Extra_arg.t))).
Extract Inlined Constant extra_args => "Continuation_extra_params_and_args.extra_args".

(* Not in the interface: an empty module with the name of this file. With
   it Rocq's extraction does not open this file's module in the files that
   use it, and prints each of its names in full. So what the real module
   has, and these declarations do not have, hides no other name there. *)
Module Continuation_extra_params_and_args. End Continuation_extra_params_and_args.
