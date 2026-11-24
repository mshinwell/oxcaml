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

(* This file follows middle_end/flambda2/simplify/env/continuation_uses.ml at
   commit ecc5c0d968c892b4312065caef0f19ffffa042a9, definition by definition
   under the compiler's names; the numbers in the comments are the lines of
   that file. What is not from that file: the form (the monad, the
   temporaries [tmpN] and their order, the arguments by place) is that of
   GUIDE.md. No proof. *)

From SimplifyPort Require Import Port_monad.
From SimplifyPort.decl Require Apply_cont_rewrite_id Continuation
  Downwards_env Flambda2_types Flambda_arity Flambda_colours
  Flambda_features Flambda_kind Format List Misc One_continuation_use
  Printexc Stdlib_.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* PORT-GAP(verbatim): 17-19, the three abbreviations of modules are the
   compiler's text, and the Rocq text below writes the modules' own names.
   As Rocq modules ([Module T := Flambda2_types.]) they make Rocq write
   [open Flambda2_types] and [open Tag] in the extracted file, and after
   them OCaml reads the type [Map.t] of line 91, which Rocq prints after
   [open Apply_cont_rewrite_id], as [Tag.Map.t]. *)
(*OCAML
module DE = Downwards_env
module T = Flambda2_types
module U = One_continuation_use
OCAML*)

(* 21-25 *)
Record t : Type :=
  { continuation : Continuation.t;
    arity : Flambda_arity.t_Unarized;
    uses : list One_continuation_use.t
  }.

(* 27 *)
Definition create (continuation : Continuation.t) (arity : Flambda_arity.t_Unarized)
    : M Continuation_uses.t :=
  ret {| continuation := continuation; arity := arity; uses := [] |}.

(* 29-37 *)
(* PORT-GAP(loose): the attribute [@ocamlformat "disable"] is not kept, and
   the record pattern of the parameter is a match. *)
Definition print (ppf : Format.formatter) (t : Continuation_uses.t) : M unit :=
  match t with
  | {| continuation := continuation; arity := arity; uses := uses |} =>
    (* PORT-GAP(papp): [Format.pp_print_list] is given its first two
       arguments only. *)
    let! tmp1 :=
      papp2 Format.pp_print_list (Some Format.pp_print_space)
        One_continuation_use.print
    in
    Format.fprintf6 ppf
      "@[<hov 1>(@[<hov 1>(continuation@ %a)@]@ @[<hov 1>(arity@ %a)@]@ @[<hov 1>(uses@ %a)@])@]"
      Continuation.print continuation Flambda_arity.print arity tmp1 uses
  end.

(* PORT-GAP(update): 48, [{ t with uses }]. *)
Definition update_uses (t : Continuation_uses.t)
    (uses : list One_continuation_use.t) : Continuation_uses.t :=
  {| continuation := t.(continuation);
     arity := t.(arity);
     uses := uses
  |}.
Extract Inlined Constant update_uses =>
  "(fun t uses -> { t with uses = uses })".

(* 39-59 *)
Definition add_use (t : Continuation_uses.t) (use : One_continuation_use.t)
    : M Continuation_uses.t :=
  try_with
    (fun _ =>
      let* arity :=
        let! tmp1 := One_continuation_use.arg_types use in
        Flambda2_types.arity_of_list tmp1
      in
      (* Kinds will always match at join points *)
      (let! tmp1 :=
         Flambda_arity.equal_ignoring_subkinds arity
           t.(Continuation_uses.arity)
       in
       if negb tmp1
       then
         fatal_errorf4
           "Arity of use (%a) doesn't match continuation's arity (%a)"
           Flambda_arity.print arity Flambda_arity.print
           t.(Continuation_uses.arity)
       else ret tt) ;;
      ret (update_uses t (use :: t.(uses))))
    Fatal_error
    (fun _ =>
      let* bt := Printexc.get_raw_backtrace tt in
      (let! tmp1 := One_continuation_use.env_at_use use in
       let! tmp2 := One_continuation_use.arg_types use in
       (* PORT-GAP(papp): [Format.pp_print_list] is given its first two
          arguments only. *)
       let! tmp3 :=
         papp2 Format.pp_print_list (Some Format.pp_print_space)
           Flambda2_types.print
       in
       Format.eprintf10
         "
%tContext is:%t adding use of %a with arg types@ (%a);@ existing uses:@ %a; environment:@ %a"
         Flambda_colours.error Flambda_colours.pop Continuation.print
         t.(continuation) tmp3 tmp2 print t Downwards_env.print tmp1) ;;
      Printexc.raise_with_backtrace (exn_make Fatal_error tt) bt).

(* 61-78 *)
Definition union (t1 t2 : Continuation_uses.t) : M Continuation_uses.t :=
  (let! tmp1 := Continuation.equal t1.(continuation) t2.(continuation) in
   if negb tmp1
   then
     fatal_errorf8
       "Cannot union continuation uses for different continuations %a and %a.@ Continuation uses t1:@ %a@ and@ t2:@ %a"
       Continuation.print t1.(continuation) Continuation.print
       t2.(continuation) print t1 print t2
   else ret tt) ;;
  (let! tmp1 := Flambda_features.kind_checks tt in
   let! tmp2 :=
     and_then tmp1
       (let! tmp3 :=
          Flambda_arity.equal_ignoring_subkinds t1.(arity) t2.(arity)
        in
        ret (negb tmp3))
   in
   if tmp2
   then
     fatal_errorf8
       "Arity of continuation uses (%a) doesn't match arity of continuation uses (%a).  Continuation uses t1:@ %a@ and@ t2:@ %a"
       Flambda_arity.print t1.(arity) Flambda_arity.print t2.(arity) print t1
       print t2
   else ret tt) ;;
  ret
    {| continuation := t1.(continuation);
       arity := t1.(arity);
       uses := t1.(uses) ++ t2.(uses)
    |}.

(* 80 *)
Definition number_of_uses (t : Continuation_uses.t) : M int :=
  List.length t.(uses).

(* PORT-GAP(loose): 82, [arity] is the projection [arity] of the record
   [t], which Rocq prints as [let arity t = t.arity] after the type. *)

(* 84 *)
Definition get_uses (t : Continuation_uses.t)
    : M (list One_continuation_use.t) :=
  ret t.(uses).

(* 86-89 *)
Record arg_at_use : Type :=
  { arg_type : Flambda2_types.t;
    typing_env : Flambda2_types.Typing_env.t
  }.

(* 91 *)
Definition arg_types_by_use_id : Type :=
  list (Apply_cont_rewrite_id.Map.t arg_at_use).

(* 93-94 *)
(* PORT-GAP(loose): the record pattern of the parameter is a match. *)
Definition print_arg_type_at_use (ppf : Format.formatter) (a : arg_at_use)
    : M unit :=
  match a with
  | {| arg_type := arg_type; typing_env := _ |} =>
    Flambda2_types.print ppf arg_type
  end.

(* 96-100 *)
Definition add_value_to_arg_map
    (arg_map : Apply_cont_rewrite_id.Map.t arg_at_use)
    (arg_type : Flambda2_types.t) (use : One_continuation_use.t)
    : M (Apply_cont_rewrite_id.Map.t arg_at_use) :=
  let* env_at_use := One_continuation_use.env_at_use use in
  let* typing_env := Downwards_env.typing_env env_at_use in
  let& arg_at_use := {| arg_type := arg_type; typing_env := typing_env |} in
  let! tmp1 := One_continuation_use.id use in
  Apply_cont_rewrite_id.Map.add tmp1 arg_at_use arg_map.

(* 102-110 *)
Definition add_uses_to_arg_maps (arg_maps : arg_types_by_use_id)
    (uses : list One_continuation_use.t) : M arg_types_by_use_id :=
  List.fold_left
    (fun arg_maps use =>
      let* arg_types := One_continuation_use.arg_types use in
      let! tmp1 :=
        Misc.Stdlib.List.map2_prefix
          (fun arg_map arg_type => add_value_to_arg_map arg_map arg_type use)
          arg_maps arg_types
      in
      Stdlib_.fst tmp1)
    arg_maps uses.

(* 112-115 *)
Definition empty_arg_maps (arity : Flambda_arity.t_Unarized) : M arg_types_by_use_id :=
  let! tmp1 := Flambda_arity.unarized_components arity in
  List.map (fun _ => ret Apply_cont_rewrite_id.Map.empty) tmp1.

(* 117-118 *)
Definition get_arg_types_by_use_id (t : Continuation_uses.t)
    : M arg_types_by_use_id :=
  let! tmp1 := empty_arg_maps t.(arity) in
  add_uses_to_arg_maps tmp1 t.(uses).

(* We want to get the arg_types_by_use_id for the invariant params only of a
   mutually-recursive continuation group. In this case, the arguments we want
   are a prefix of the actual argument lists. *)
(* 123-140. [Misc.Stdlib.List.is_prefix ~equal prefix ~of_]: the arguments
   are in the order of the interface. *)
Definition get_arg_types_by_use_id_for_invariant_params
    (arity : Flambda_arity.t_Unarized) (l : list Continuation_uses.t)
    : M arg_types_by_use_id :=
  let! tmp1 := empty_arg_maps arity in
  List.fold_left
    (fun arg_maps t =>
      (let! tmp2 :=
         Flambda_arity.unarized_components t.(Continuation_uses.arity)
       in
       let! tmp3 := List.map Flambda_kind.With_subkind.kind tmp2 in
       let! tmp4 := Flambda_arity.unarized_components arity in
       let! tmp5 := List.map Flambda_kind.With_subkind.kind tmp4 in
       let! tmp6 :=
         Misc.Stdlib.List.is_prefix Flambda_kind.equal tmp5 tmp3
       in
       if negb tmp6
       then
         fatal_errorf4
           "Arity of invariant params@ (%a) is not a prefix of the arity of the continuation uses@ (%a)"
           Flambda_arity.print arity Flambda_arity.print
           t.(Continuation_uses.arity)
       else ret tt) ;;
      add_uses_to_arg_maps arg_maps t.(uses))
    tmp1 l.

(* 142-145 *)
Definition get_use_ids (t : Continuation_uses.t)
    : M Apply_cont_rewrite_id.Set_.t :=
  List.fold_left
    (fun uses use =>
      let! tmp1 := One_continuation_use.id use in
      Apply_cont_rewrite_id.Set_.add tmp1 uses)
    Apply_cont_rewrite_id.Set_.empty t.(uses).

(* 147-153 *)
Definition get_typing_env_no_more_than_one_use (t : Continuation_uses.t)
    : M (option Flambda2_types.Typing_env.t) :=
  match t.(uses) with
  | [] => ret None
  | [use] =>
    let! tmp1 := One_continuation_use.env_at_use use in
    let! tmp2 := Downwards_env.typing_env tmp1 in
    ret (Some tmp2)
  | _ :: _ =>
    fatal_errorf2 "Only zero or one continuation use(s) expected:@ %a" print t
  end.

(* 155-156 *)
Definition mark_non_inlinable (t : Continuation_uses.t)
    : M Continuation_uses.t :=
  let! tmp1 := List.map One_continuation_use.mark_non_inlinable t.(uses) in
  ret (update_uses t tmp1).

(* 158 *)
Definition clear_uses (t : Continuation_uses.t) : M Continuation_uses.t :=
  ret (update_uses t []).
