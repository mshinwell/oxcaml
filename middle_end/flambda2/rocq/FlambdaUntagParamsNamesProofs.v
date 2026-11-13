(******************************************************************************
 *                                  OxCaml                                    *
 * -------------------------------------------------------------------------- *
 *                               MIT License                                  *
 *                                                                            *
 * Copyright (c) 2026 Jane Street Group LLC                                   *
 * opensource-contacts@janestreet.com                                         *
 *                                                                            *
 * Permission is hereby granted, free of charge, to any person obtaining a    *
 * copy of this software and associated documentation files (the "Software"), *
 * to deal in the Software without restriction, including without limitation  *
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
 * and/or sell copies of the Software, and to permit persons to whom the      *
 * Software is furnished to do so, subject to the following conditions:       *
 *                                                                            *
 * The above copyright notice and this permission notice shall be included    *
 * in all copies or substantial portions of the Software.                     *
 *                                                                            *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
 * DEALINGS IN THE SOFTWARE.                                                  *
 ******************************************************************************)


(* FlambdaUntagParamsSpec.untag_params commutes with renaming and keeps
   scope: the lemmas from which FlambdaValidatorEquivarianceProofs.v
   and FlambdaStaticsScopeProofs.v prove the two statements. There is
   no statement here, and nothing here needs review.

   The pass compares names by equality only and makes none. So each of
   its functions gives, on a renamed term, the renamed result: the
   rewrite and the test for renamed positions, and the positions that
   the validation uses, which are computed from the term. For the
   scope: the arguments of an application are the same in another
   order, but for constants; the parameters of a handler are the same
   in another order; and the [Let] of a parameter mentions the
   variable that the untagging mentioned. *)

From Stdlib Require Import ZArith List Bool Arith Permutation.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList.
From OxCamlFlambda2 Require Import FlambdaKindModel FlambdaModel
  FlambdaMapSpec FlambdaMapProofs FlambdaPrimitiveModel FlambdaSemanticsSpec
  FlambdaNominalSpec FlambdaNominalProofs FlambdaAlphaProofs
  FlambdaEquivarianceSpec FlambdaEquivarianceProofs FlambdaBindersSpec
  FlambdaNormaliseSpec FlambdaValidatorEquivarianceSpec
  FlambdaValidatorEquivarianceBaseProofs FlambdaScopedProofs
  FlambdaUntagParamsSpec FlambdaUntagParamsProofs.
Import ListNotations.

(* ======================================================================== *)
(* The positions renamed                                                    *)
(* ======================================================================== *)

(* A map keyed by continuations, with its keys renamed: the positions,
   and the positions that the test refuses. *)
Definition rename_keyed {A : Type} (r : renaming)
    (l : list (continuation * A)) : list (continuation * A) :=
  map (fun entry => (rename_continuation r (fst entry), snd entry)) l.

Lemma positions_of_renamed (r : renaming) (sites : positions)
    (k : continuation) :
  positions_of (rename_keyed r sites) (rename_continuation r k)
  = positions_of sites k.
Proof.
  unfold positions_of, rename_keyed.
  induction sites as [ | [k' us] sites IH]; [ reflexivity | ].
  cbn [map fst snd]. rewrite !lookup_cons, rename_continuation_eqb.
  destruct (Pos.eqb k k'); [ reflexivity | exact IH ].
Qed.

Definition rename_handlers (r : renaming)
    (handlers : list (continuation * continuation_handler))
    : list (continuation * continuation_handler) :=
  map (fun '(k, h) => (rename_continuation r k, rename_handler r h)) handlers.

Lemma active_under_renamed (r : renaming) (sites active : positions)
    (handlers : list (continuation * continuation_handler)) :
  active_under (rename_keyed r sites) (rename_handlers r handlers)
    (rename_keyed r active)
  = rename_keyed r (active_under sites handlers active).
Proof.
  unfold active_under, rename_keyed, rename_handlers.
  rewrite map_app, !map_map. f_equal.
  apply map_ext. intros [k h]. cbn [fst snd].
  fold (rename_keyed r sites). rewrite positions_of_renamed. reflexivity.
Qed.

(* ======================================================================== *)
(* The rewrite commutes with renaming                                       *)
(* ======================================================================== *)

Lemma untag_simple_renamed (r : renaming) (s : simple) :
  untag_simple (rename_simple r s) = rename_simple r (untag_simple s).
Proof. destruct s as [x | sym | c]; [ | | destruct c ]; reflexivity. Qed.

Lemma untag_args_renamed (r : renaming) (us : list nat)
    (args : list simple) :
  untag_args us (map (rename_simple r) args)
  = map (rename_simple r) (untag_args us args).
Proof.
  unfold untag_args.
  rewrite kept_from_map, moved_from_map, map_app, map_rev, !map_map.
  do 2 f_equal. apply map_ext. intros s. apply untag_simple_renamed.
Qed.

Lemma untag_apply_cont_renamed (r : renaming) (active : positions)
    (ac : apply_cont) :
  untag_apply_cont (rename_keyed r active) (rename_apply_cont r ac)
  = rename_apply_cont r (untag_apply_cont active ac).
Proof.
  unfold untag_apply_cont, rename_apply_cont.
  cbn [ac_continuation ac_args ac_trap_action].
  rewrite positions_of_renamed, untag_args_renamed. reflexivity.
Qed.

Lemma untag_of_renamed (r : renaming) (d : named) :
  untag_of (rename_named r d) = option_map (rename_variable r) (untag_of d).
Proof.
  destruct d as [s | [[] | | | ] [ | [x | sym | c] [ | a args]] | | | | | ];
    reflexivity.
Qed.

Lemma untag_named_renamed (r : renaming) (untagged : list variable)
    (d : named) :
  untag_named (map (rename_variable r) untagged) (rename_named r d)
  = rename_named r (untag_named untagged d).
Proof.
  unfold untag_named. rewrite untag_of_renamed.
  destruct (untag_of d) as [p | ]; cbn [option_map]; [ | reflexivity ].
  rewrite among_rename_variable. destruct (among p untagged); reflexivity.
Qed.

Lemma untag_params_list_renamed (r : renaming) (us : list nat)
    (params : list variable) :
  untag_params_list us (map (rename_variable r) params)
  = map (rename_variable r) (untag_params_list us params).
Proof.
  unfold untag_params_list.
  rewrite kept_from_map, moved_from_map, map_app, map_rev. reflexivity.
Qed.

Lemma untagged_under_renamed (r : renaming) (us : list nat)
    (params untagged : list variable) :
  untagged_under us (map (rename_variable r) params)
    (map (rename_variable r) untagged)
  = map (rename_variable r) (untagged_under us params untagged).
Proof.
  unfold untagged_under.
  rewrite moved_from_map, map_app,
    (without_map_injective (rename_variable r) (rename_variable_eqb r)).
  reflexivity.
Qed.

Lemma without_one_renamed (r : renaming) (x : variable)
    (untagged : list variable) :
  without [rename_variable r x] (map (rename_variable r) untagged)
  = map (rename_variable r) (without [x] untagged).
Proof.
  exact
    (without_map_injective (rename_variable r) (rename_variable_eqb r) [x]
       untagged).
Qed.

Fixpoint untag_expr_renamed (r : renaming) (sites active : positions)
    (untagged : list variable) (e : expr) {struct e} :
  untag_expr (rename_keyed r sites) (rename_keyed r active)
    (map (rename_variable r) untagged) (rename_expr r e)
  = rename_expr r (untag_expr sites active untagged e)
with untag_handler_renamed (r : renaming) (sites active : positions)
    (untagged : list variable) (us : list nat) (h : continuation_handler)
    {struct h} :
  untag_handler (rename_keyed r sites) (rename_keyed r active)
    (map (rename_variable r) untagged) us (rename_handler r h)
  = rename_handler r (untag_handler sites active untagged us h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [rename_expr untag_expr]; try reflexivity.
    + rewrite untag_named_renamed, without_one_renamed, untag_expr_renamed.
      reflexivity.
    + rewrite untag_expr_renamed. reflexivity.
    + rewrite positions_of_renamed, untag_handler_renamed.
      rewrite
        <- (untag_expr_renamed r sites ((k', positions_of sites k') :: active)).
      reflexivity.
    + fold (rename_handlers r handlers).
      rewrite active_under_renamed, untag_expr_renamed. f_equal.
      generalize (active_under sites handlers active). intros active'.
      unfold rename_handlers.
      induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
      cbn [map].
      rewrite positions_of_renamed, untag_handler_renamed, IH. reflexivity.
    + rewrite untag_apply_cont_renamed. reflexivity.
    + f_equal. induction arms as [ | [n ac] arms IH]; [ reflexivity | ].
      cbn [map fst snd]. rewrite untag_apply_cont_renamed, IH. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler untag_handler].
    rewrite untag_params_list_renamed, untagged_under_renamed,
      untag_expr_renamed.
    reflexivity.
Qed.

(* ======================================================================== *)
(* The test commutes with renaming                                          *)
(* ======================================================================== *)

Lemma none_in_renamed (r : renaming) (untagged : list variable)
    (mentions mentions' : variable -> bool) :
  (∀ p : variable, mentions' (rename_variable r p) = mentions p) ->
  none_in (map (rename_variable r) untagged) mentions'
  = none_in untagged mentions.
Proof.
  intros Hmentions. unfold none_in.
  induction untagged as [ | p untagged IH]; [ reflexivity | ].
  cbn [map forallb]. rewrite Hmentions, IH. reflexivity.
Qed.

Lemma untagged_arg_renamed (r : renaming) (untagged : list variable)
    (s : simple) :
  untagged_arg (map (rename_variable r) untagged) (rename_simple r s)
  = untagged_arg untagged s.
Proof.
  destruct s as [x | sym | c]; cbn [rename_simple untagged_arg];
    [ apply among_rename_variable | reflexivity | reflexivity ].
Qed.

Lemma args_ok_renamed (r : renaming) (untagged : list variable)
    (us : list nat) (args : list simple) :
  args_ok (map (rename_variable r) untagged) us (map (rename_simple r) args)
  = args_ok untagged us args.
Proof.
  unfold args_ok. rewrite kept_from_map, moved_from_map. f_equal.
  - apply none_in_renamed. intros p. apply var_in_simples_equivariant.
  - induction (moved_from us 0 args) as [ | s rest IH]; [ reflexivity | ].
    cbn [map forallb]. rewrite untagged_arg_renamed, IH. reflexivity.
Qed.

Lemma apply_cont_ok_renamed (r : renaming) (active : positions)
    (untagged : list variable) (ac : apply_cont) :
  apply_cont_ok (rename_keyed r active) (map (rename_variable r) untagged)
    (rename_apply_cont r ac)
  = apply_cont_ok active untagged ac.
Proof.
  unfold apply_cont_ok, rename_apply_cont. cbn [ac_continuation ac_args].
  rewrite positions_of_renamed. apply args_ok_renamed.
Qed.

Lemma reads_untagged_renamed (r : renaming) (untagged : list variable)
    (d : named) :
  reads_untagged (map (rename_variable r) untagged) (rename_named r d)
  = reads_untagged untagged d.
Proof.
  unfold reads_untagged. rewrite untag_of_renamed.
  destruct (untag_of d) as [p | ]; cbn [option_map]; [ | reflexivity ].
  apply among_rename_variable.
Qed.

Lemma named_ok_renamed (r : renaming) (untagged : list variable)
    (d : named) :
  named_ok (map (rename_variable r) untagged) (rename_named r d)
  = named_ok untagged d.
Proof.
  unfold named_ok. rewrite reads_untagged_renamed. f_equal.
  apply none_in_renamed. intros p. apply var_in_named_equivariant.
Qed.

Lemma distinct_renamed (r : renaming) (params : list variable) :
  distinct (map (rename_variable r) params) = distinct params.
Proof.
  induction params as [ | x params IH]; [ reflexivity | ].
  cbn [map distinct]. rewrite among_rename_variable, IH. reflexivity.
Qed.

Lemma handler_fits_renamed (r : renaming) (us : list nat)
    (params : list variable) (metadata : handler_metadata) :
  handler_fits us (map (rename_variable r) params) metadata
  = handler_fits us params metadata.
Proof. unfold handler_fits. rewrite distinct_renamed. reflexivity. Qed.

Lemma no_positions_renamed (r : renaming) (active : positions)
    (k : continuation) :
  no_positions (rename_keyed r active) (rename_continuation r k)
  = no_positions active k.
Proof. unfold no_positions. rewrite positions_of_renamed. reflexivity. Qed.

Lemma exn_extra_simples_renamed (r : renaming) (ap : apply_expr) :
  exn_extra_simples (rename_apply r ap)
  = map (rename_simple r) (exn_extra_simples ap).
Proof.
  unfold exn_extra_simples, rename_apply. cbn [ap_exn_extra_args].
  rewrite !map_map. reflexivity.
Qed.

Fixpoint untag_ok_renamed (r : renaming) (sites active : positions)
    (untagged : list variable) (e : expr) {struct e} :
  untag_ok (rename_keyed r sites) (rename_keyed r active)
    (map (rename_variable r) untagged) (rename_expr r e)
  = untag_ok sites active untagged e
with handler_ok_renamed (r : renaming) (sites active : positions)
    (untagged : list variable) (us : list nat) (h : continuation_handler)
    {struct h} :
  handler_ok (rename_keyed r sites) (rename_keyed r active)
    (map (rename_variable r) untagged) us (rename_handler r h)
  = handler_ok sites active untagged us h.
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [rename_expr untag_ok]; try reflexivity.
    + rewrite named_ok_renamed, without_one_renamed, untag_ok_renamed.
      reflexivity.
    + rewrite untag_ok_renamed. f_equal.
      apply none_in_renamed. intros p. apply existsb_map_with.
      intros binding. apply var_in_static_binding_equivariant.
    + rewrite positions_of_renamed, handler_ok_renamed.
      rewrite
        <- (untag_ok_renamed r sites ((k', positions_of sites k') :: active)).
      reflexivity.
    + fold (rename_handlers r handlers).
      rewrite active_under_renamed, untag_ok_renamed. f_equal.
      generalize (active_under sites handlers active). intros active'.
      unfold rename_handlers.
      induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
      cbn [map forallb].
      rewrite positions_of_renamed, handler_ok_renamed, IH. reflexivity.
    + cbn [rename_apply ap_callee ap_args ap_continuation ap_exn_continuation].
      rewrite !no_positions_renamed. do 2 f_equal.
      apply none_in_renamed. intros p.
      fold (rename_apply r ap). rewrite exn_extra_simples_renamed.
      rewrite var_in_simple_equivariant, !var_in_simples_equivariant.
      reflexivity.
    + apply apply_cont_ok_renamed.
    + f_equal.
      * apply none_in_renamed. intros p. apply var_in_simple_equivariant.
      * induction arms as [ | [n ac] arms IH]; [ reflexivity | ].
        cbn [map forallb fst snd]. rewrite apply_cont_ok_renamed, IH.
        reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_ok].
    rewrite handler_fits_renamed, untagged_under_renamed, untag_ok_renamed.
    reflexivity.
Qed.

Lemma untag_at_renamed (r : renaming) (sites : positions) (e : expr) :
  untag_at (rename_keyed r sites) (rename_expr r e)
  = rename_expr r (untag_at sites e).
Proof.
  unfold untag_at.
  rewrite (untag_ok_renamed r sites [] [] e : untag_ok _ [] [] _ = _).
  destruct (untag_ok sites [] [] e); [ | reflexivity ].
  exact (untag_expr_renamed r sites [] [] e).
Qed.

(* ======================================================================== *)
(* The positions that the validation uses commute with renaming             *)
(* ======================================================================== *)

Lemma rename_keyed_app {A : Type} (r : renaming)
    (l l' : list (continuation * A)) :
  rename_keyed r (l ++ l') = rename_keyed r l ++ rename_keyed r l'.
Proof. apply map_app. Qed.

Fixpoint candidates_renamed (r : renaming) (e : expr) {struct e} :
  candidates (rename_expr r e) = rename_keyed r (candidates e)
with handler_candidates_renamed (r : renaming) (k : continuation)
    (h : continuation_handler) {struct h} :
  handler_candidates (rename_continuation r k) (rename_handler r h)
  = rename_keyed r (handler_candidates k h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [rename_expr candidates]; try reflexivity.
    + apply candidates_renamed.
    + apply candidates_renamed.
    + rewrite handler_candidates_renamed, candidates_renamed, rename_keyed_app.
      reflexivity.
    + rewrite candidates_renamed, rename_keyed_app. f_equal.
      induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
      cbn [map flat_map].
      rewrite handler_candidates_renamed, IH, rename_keyed_app. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_candidates].
    rewrite candidates_renamed. reflexivity.
Qed.

(* The origins of the untagged variables, renamed. *)
Definition rename_origin (r : renaming) (origin : origin_map) : origin_map :=
  map
    (fun entry =>
       (rename_variable r (fst entry),
        (rename_continuation r (fst (snd entry)), snd (snd entry))))
    origin.

Lemma rename_origin_app (r : renaming) (origin origin' : origin_map) :
  rename_origin r (origin ++ origin')
  = rename_origin r origin ++ rename_origin r origin'.
Proof. apply map_app. Qed.

Lemma map_fst_rename_origin (r : renaming) (origin : origin_map) :
  map fst (rename_origin r origin)
  = map (rename_variable r) (map fst origin).
Proof. unfold rename_origin. rewrite !map_map. reflexivity. Qed.

Lemma origins_renamed (r : renaming) (origin : origin_map)
    (mentions mentions' : variable -> bool) :
  (∀ x : variable, mentions' (rename_variable r x) = mentions x) ->
  origins (rename_origin r origin) mentions'
  = rename_keyed r (origins origin mentions).
Proof.
  intros Hmentions. unfold origins, rename_origin.
  induction origin as [ | [x [k i]] origin IH]; [ reflexivity | ].
  cbn [map flat_map fst snd]. rewrite Hmentions, IH, rename_keyed_app.
  destruct (mentions x); reflexivity.
Qed.

Lemma unbind_renamed (r : renaming) (x : variable) (origin : origin_map) :
  unbind (rename_variable r x) (rename_origin r origin)
  = rename_origin r (unbind x origin).
Proof.
  unfold unbind, rename_origin.
  induction origin as [ | [y [k i]] origin IH]; [ reflexivity | ].
  cbn [map filter fst snd]. rewrite rename_variable_eqb.
  destruct (Pos.eqb x y); cbn [negb map fst snd]; rewrite IH; reflexivity.
Qed.

Lemma all_of_renamed (r : renaming) (active : positions) (k : continuation) :
  all_of (rename_keyed r active) (rename_continuation r k)
  = rename_keyed r (all_of active k).
Proof.
  unfold all_of. rewrite positions_of_renamed. unfold rename_keyed.
  rewrite map_map. reflexivity.
Qed.

Lemma params_origins_renamed (r : renaming) (k : continuation)
    (us : list nat) (params : list variable) :
  ∀ i : nat,
    params_origins (rename_continuation r k) us i
      (map (rename_variable r) params)
    = rename_origin r (params_origins k us i params).
Proof.
  induction params as [ | p params IH]; intros i; [ reflexivity | ].
  cbn [map params_origins].
  destruct (at_position us i); cbn [rename_origin map fst snd];
    rewrite IH; reflexivity.
Qed.

Lemma origins_under_renamed (r : renaming) (k : continuation)
    (us : list nat) (params : list variable) (origin : origin_map) :
  origins_under (rename_continuation r k) us (map (rename_variable r) params)
    (rename_origin r origin)
  = rename_origin r (origins_under k us params origin).
Proof.
  unfold origins_under.
  rewrite params_origins_renamed, rename_origin_app. f_equal.
  unfold rename_origin.
  induction origin as [ | [x [k' i]] origin IH]; [ reflexivity | ].
  cbn [map filter fst snd]. rewrite among_rename_variable.
  destruct (among x params); cbn [negb map fst snd]; rewrite IH;
    reflexivity.
Qed.

Lemma args_blame_renamed (r : renaming) (origin : origin_map)
    (k : continuation) (us : list nat) (args : list simple) :
  ∀ i : nat,
    args_blame (rename_origin r origin) (rename_continuation r k) us i
      (map (rename_simple r) args)
    = rename_keyed r (args_blame origin k us i args).
Proof.
  induction args as [ | a args IH]; intros i; [ reflexivity | ].
  cbn [map args_blame]. rewrite IH, rename_keyed_app. f_equal.
  destruct (at_position us i).
  - rewrite map_fst_rename_origin, untagged_arg_renamed.
    destruct (untagged_arg (map fst origin) a); reflexivity.
  - apply origins_renamed. intros x. apply var_in_simple_equivariant.
Qed.

Lemma apply_cont_blame_renamed (r : renaming) (active : positions)
    (origin : origin_map) (ac : apply_cont) :
  apply_cont_blame (rename_keyed r active) (rename_origin r origin)
    (rename_apply_cont r ac)
  = rename_keyed r (apply_cont_blame active origin ac).
Proof.
  unfold apply_cont_blame, rename_apply_cont.
  cbn [ac_continuation ac_args].
  rewrite positions_of_renamed. apply args_blame_renamed.
Qed.

Fixpoint blame_renamed (r : renaming) (sites active : positions)
    (origin : origin_map) (e : expr) {struct e} :
  blame (rename_keyed r sites) (rename_keyed r active)
    (rename_origin r origin) (rename_expr r e)
  = rename_keyed r (blame sites active origin e)
with handler_blame_renamed (r : renaming) (sites active : positions)
    (origin : origin_map) (k : continuation) (h : continuation_handler)
    {struct h} :
  handler_blame (rename_keyed r sites) (rename_keyed r active)
    (rename_origin r origin) (rename_continuation r k) (rename_handler r h)
  = rename_keyed r (handler_blame sites active origin k h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [rename_expr blame]; try reflexivity.
    + rewrite map_fst_rename_origin, reads_untagged_renamed, unbind_renamed,
        blame_renamed, rename_keyed_app.
      f_equal.
      destruct (reads_untagged (map fst origin) d); [ reflexivity | ].
      apply origins_renamed. intros x. apply var_in_named_equivariant.
    + rewrite blame_renamed, rename_keyed_app. f_equal.
      apply origins_renamed. intros x. apply existsb_map_with.
      intros binding. apply var_in_static_binding_equivariant.
    + rewrite positions_of_renamed, handler_blame_renamed, rename_keyed_app.
      rewrite
        <- (blame_renamed r sites ((k', positions_of sites k') :: active)).
      reflexivity.
    + fold (rename_handlers r handlers).
      rewrite active_under_renamed, blame_renamed, rename_keyed_app. f_equal.
      generalize (active_under sites handlers active). intros active'.
      unfold rename_handlers.
      induction handlers as [ | [k' hh] handlers IH]; [ reflexivity | ].
      cbn [map flat_map].
      rewrite handler_blame_renamed, IH, rename_keyed_app. reflexivity.
    + cbn [rename_apply ap_callee ap_args ap_continuation ap_exn_continuation].
      rewrite !all_of_renamed, !rename_keyed_app. f_equal.
      apply origins_renamed. intros x.
      fold (rename_apply r ap). rewrite exn_extra_simples_renamed.
      rewrite var_in_simple_equivariant, !var_in_simples_equivariant.
      reflexivity.
    + apply apply_cont_blame_renamed.
    + rewrite rename_keyed_app. f_equal.
      * apply origins_renamed. intros x. apply var_in_simple_equivariant.
      * induction arms as [ | [n ac] arms IH]; [ reflexivity | ].
        cbn [map flat_map fst snd].
        rewrite apply_cont_blame_renamed, IH, rename_keyed_app. reflexivity.
  - destruct h as [params metadata handler].
    cbn [rename_handler handler_blame].
    rewrite positions_of_renamed, handler_fits_renamed, origins_under_renamed,
      blame_renamed, rename_keyed_app.
    f_equal.
    destruct (handler_fits (positions_of sites k) params metadata);
      [ reflexivity | ].
    unfold rename_keyed. rewrite map_map. reflexivity.
Qed.

Lemma blamed_renamed (r : renaming) (refused : list (continuation * nat))
    (k : continuation) (u : nat) :
  blamed (rename_keyed r refused) (rename_continuation r k) u
  = blamed refused k u.
Proof.
  unfold blamed, rename_keyed. apply existsb_map_with. intros [k' u'].
  cbn [fst snd]. rewrite rename_continuation_eqb. reflexivity.
Qed.

Lemma prune_renamed (r : renaming) (refused : list (continuation * nat))
    (sites : positions) :
  prune (rename_keyed r refused) (rename_keyed r sites)
  = rename_keyed r (prune refused sites).
Proof.
  unfold prune. unfold rename_keyed at 2 3. rewrite !map_map.
  apply map_ext. intros [k us]. cbn [fst snd]. f_equal.
  apply filter_ext. intros u. rewrite blamed_renamed. reflexivity.
Qed.

Lemma settle_renamed (r : renaming) (fuel : nat) :
  ∀ (sites : positions) (e : expr),
    settle_positions fuel (rename_keyed r sites) (rename_expr r e)
    = rename_keyed r (settle_positions fuel sites e).
Proof.
  induction fuel as [ | fuel IH]; intros sites e; [ reflexivity | ].
  cbn [settle_positions].
  rewrite (blame_renamed r sites [] [] e : blame _ [] [] _ = _).
  destruct (blame sites [] [] e) as [ | refused0 refused] eqn:Hblame;
    [ reflexivity | ].
  cbn [rename_keyed map].
  exact (eq_trans
    (f_equal (fun s => settle_positions fuel s (rename_expr r e))
       (prune_renamed r (refused0 :: refused) sites))
    (IH (prune (refused0 :: refused) sites) e)).
Qed.

Lemma count_positions_renamed (r : renaming) (sites : positions) :
  count_positions (rename_keyed r sites) = count_positions sites.
Proof.
  unfold count_positions, rename_keyed. rewrite map_map. f_equal.
  apply map_ext. intros [k us]. reflexivity.
Qed.

Lemma untag_positions_renamed (r : renaming) (e : expr) :
  untag_positions (rename_expr r e) = rename_keyed r (untag_positions e).
Proof.
  unfold untag_positions.
  rewrite candidates_renamed, count_positions_renamed. apply settle_renamed.
Qed.

Lemma untag_params_renamed : rewrite_equivariant untag_params.
Proof.
  intros r e. unfold untag_params.
  rewrite untag_positions_renamed. apply untag_at_renamed.
Qed.

(* ======================================================================== *)
(* The pass keeps scope                                                     *)
(* ======================================================================== *)

Lemma in_kept_from {A : Type} (us : list nat) (a : A) (l : list A) :
  ∀ i : nat, In a (kept_from us i l) -> In a l.
Proof.
  induction l as [ | b l IH]; intros i; cbn [kept_from];
    [ intros H; exact H | ].
  destruct (at_position us i).
  - intros H. right. exact (IH _ H).
  - intros [H | H]; [ left; exact H | right; exact (IH _ H) ].
Qed.

Lemma in_moved_from {A : Type} (us : list nat) (a : A) (l : list A) :
  ∀ i : nat, In a (moved_from us i l) -> In a l.
Proof.
  induction l as [ | b l IH]; intros i; cbn [moved_from];
    [ intros H; exact H | ].
  destruct (at_position us i).
  - intros [H | H]; [ left; exact H | right; exact (IH _ H) ].
  - intros H. right. exact (IH _ H).
Qed.

Lemma untag_apply_cont_free_variables (active : positions)
    (ac : apply_cont) :
  incl (free_variables_of_apply_cont (untag_apply_cont active ac))
    (free_variables_of_apply_cont ac).
Proof.
  unfold free_variables_of_apply_cont, free_variables_of_simples,
    untag_apply_cont, untag_args.
  cbn [ac_args]. intros a Ha. apply in_flat_map in Ha as (s & Hs & Ha).
  apply in_app_or in Hs as [Hs | Hs].
  - apply in_flat_map. exists s.
    split; [ exact (in_kept_from _ s _ 0 Hs) | exact Ha ].
  - apply in_rev in Hs. apply in_map_iff in Hs as (s0 & <- & Hs0).
    apply in_flat_map. exists s0.
    split; [ exact (in_moved_from _ s0 _ 0 Hs0) | ].
    destruct s0 as [x | sym | c]; [ exact Ha | exact Ha | ].
    destruct c; exact Ha.
Qed.

Lemma untag_apply_cont_continuations (active : positions) (ac : apply_cont) :
  apply_cont_continuations (untag_apply_cont active ac)
  = apply_cont_continuations ac.
Proof. reflexivity. Qed.

Lemma untag_named_free_variables (untagged : list variable) (d : named) :
  incl (free_variables_of_named (untag_named untagged d))
    (free_variables_of_named d).
Proof.
  unfold untag_named.
  destruct (untag_of d) as [p | ] eqn:Huntag; [ | apply incl_refl ].
  destruct (among p untagged); [ | apply incl_refl ].
  apply untag_of_some in Huntag. subst d. intros a Ha. exact Ha.
Qed.

Lemma untag_handler_scoped_intro (us : list nat) (params : list variable)
    (metadata : handler_metadata) (handler handler' : expr) :
  scoped handler handler' ->
  scoped_handler (Handler params metadata handler)
    (Handler (untag_params_list us params) (untag_metadata us metadata)
       handler').
Proof.
  intros Hhandler Hclosed.
  cbn [handler_code_closed free_variables_of_handler
       free_continuations_of_handler] in Hclosed |- *.
  destruct (Hhandler Hclosed) as (Hclosed' & Hv & Hk).
  split; [ exact Hclosed' | split; [ | exact Hk ] ].
  intros a Ha. apply in_without in Ha as [Ha Hnot]. apply in_without.
  split; [ exact (Hv a Ha) | ].
  intros Hin. apply Hnot. unfold untag_params_list.
  exact (Permutation_in a (kept_moved_permutation us params 0) Hin).
Qed.

Fixpoint untag_expr_scoped (sites active : positions)
    (untagged : list variable) (e : expr) {struct e} :
  scoped e (untag_expr sites active untagged e)
with untag_handler_scoped (sites active : positions)
    (untagged : list variable) (us : list nat) (h : continuation_handler)
    {struct h} :
  scoped_handler h (untag_handler sites active untagged us h).
Proof.
  - destruct e as [y kind d body | bindings body | k' hh body | handlers body
                  | ap | ac | scrutinee arms | ];
      cbn [untag_expr]; try apply scoped_refl.
    + apply scoped_let;
        [ apply untag_named_free_variables | apply untag_expr_scoped ].
    + apply scoped_let_static;
        [ apply scoped_bindings_refl | apply untag_expr_scoped ].
    + apply scoped_let_cont;
        [ apply untag_handler_scoped | apply untag_expr_scoped ].
    + apply scoped_let_cont_recursive; [ | | apply untag_expr_scoped ].
      * rewrite map_map. apply map_ext. intros [k' hh]. reflexivity.
      * generalize (active_under sites handlers active). intros active'.
        induction handlers as [ | [k' hh] handlers IH]; cbn [map];
          [ apply scoped_handlers_nil | ].
        apply scoped_handlers_cons;
          [ apply untag_handler_scoped | exact IH ].
    + intros _.
      cbn [code_closed free_variables_of_expr free_continuations_of_expr].
      split; [ reflexivity | split ].
      * apply untag_apply_cont_free_variables.
      * rewrite untag_apply_cont_continuations. apply incl_refl.
    + intros _.
      cbn [code_closed free_variables_of_expr free_continuations_of_expr].
      split; [ reflexivity | split ].
      * apply incl_app_app; [ apply incl_refl | ].
        induction arms as [ | [n ac] arms IH]; [ apply incl_refl | ].
        cbn [map flat_map snd].
        apply incl_app_app;
          [ apply untag_apply_cont_free_variables | exact IH ].
      * induction arms as [ | [n ac] arms IH]; [ apply incl_refl | ].
        cbn [map flat_map snd]. rewrite untag_apply_cont_continuations.
        apply incl_app_app; [ apply incl_refl | exact IH ].
  - destruct h as [params metadata handler]. cbn [untag_handler].
    apply untag_handler_scoped_intro, untag_expr_scoped.
Qed.

Lemma untag_at_scoped (sites : positions) (e : expr) :
  scoped e (untag_at sites e).
Proof.
  unfold untag_at.
  destruct (untag_ok sites [] [] e);
    [ apply untag_expr_scoped | apply scoped_refl ].
Qed.

Lemma untag_params_scoped (e : expr) : scoped e (untag_params e).
Proof. apply untag_at_scoped. Qed.

Lemma untag_params_scope : keeps_scope untag_params.
Proof. apply keeps_scope_intro, untag_params_scoped. Qed.
