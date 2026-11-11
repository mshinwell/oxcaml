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

(* Proofs of the statements of FlambdaUnusedParamsSpec.v. Nothing here
   needs review.

   The pass changes a binder and every application in its scope, so it
   is not a rewrite of two expressions on their own. The term and its
   result are run side by side, step for step
   (FlambdaSemanticsProofs.simulation_refines). The relation between the
   two states ([state_drops]) is:

   - the second expression is the first with parameters and arguments
     removed as some [masks] say ([drops]). This is a relation and not
     the function: where a function is called the two runs go into the
     same body, which is related to itself with every parameter kept
     ([drops_refl]), and the pass run on the term is one way of choosing
     the masks ([drop_params_drops]);
   - the variables of the two states agree on the free variables of the
     second expression. They are not the same: the first run binds the
     parameters that the second has not got;
   - each continuation name stands, in the two states, for the same
     thing or for closures whose handlers are so related, whose
     variables so agree and whose continuations are in turn so related
     ([cont_drops]), the second taking only the parameters that the
     mask of the name keeps.

   Applying two such closures, the first to the values of all the
   arguments and the second to those kept, gives states so related
   ([bind_params_masked]): the parameters removed are not free in the
   second handler. The machine tests the kinds of the values against
   those that the handler gives (FlambdaSemanticsSpec.apply_cont_value);
   the second handler gives the kinds kept, so where the values are of
   the kinds of the first, those kept are of the kinds of the second
   ([kinds_masked]). *)

From Stdlib Require Import ZArith List Bool.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaNominalSpec FlambdaCompareSpec FlambdaCompareProofs
  FlambdaNormaliseSpec FlambdaNormaliseProofs FlambdaUnusedParamsSpec.
Import ListNotations.

(* ======================================================================== *)
(* Masks                                                                    *)
(* ======================================================================== *)

(* The elements at the positions where the mask says no. *)
Definition dropped {A : Type} (mask : list bool) (l : list A) : list A :=
  keep (map negb mask) l.

(* A mask is one for these parameters and this handler: it has an entry
   for each parameter, and the parameters it removes are not free in the
   handler. *)
Definition mask_fits (mask : option (list bool)) (params : list variable)
    (handler : expr) : Prop :=
  match mask with
  | None => True
  | Some mask =>
    length mask = length params
    ∧ ∀ x : variable, x ∈ dropped mask params -> ~ var_free_in_expr x handler
  end.

Lemma mask_of_head (known : masks) (k : continuation)
    (mask : option (list bool)) :
  mask_of ((k, mask) :: known) k = mask.
Proof. unfold mask_of. simpl. rewrite Pos.eqb_refl. reflexivity. Qed.

Lemma mask_of_other (known : masks) (k k' : continuation)
    (mask : option (list bool)) :
  k' <> k -> mask_of ((k, mask) :: known) k' = mask_of known k'.
Proof.
  intros Hne. unfold mask_of. simpl.
  destruct (Pos.eqb_spec k' k); [ contradiction | reflexivity ].
Qed.

(* The masks that the handlers of a recursive [Let_cont] add: all their
   parameters are kept. *)
Definition rec_masks (handlers : list (continuation * continuation_handler))
    : masks :=
  map (fun '(k, _) => (k, None)) handlers.

Lemma mask_of_rec_masks
    (handlers : list (continuation * continuation_handler)) (known : masks)
    (k : continuation) :
  mask_of (rec_masks handlers ++ known) k
  = match lookup k handlers with
    | Some _ => None
    | None => mask_of known k
    end.
Proof.
  unfold mask_of.
  induction handlers as [ | [k' h] handlers IH]; simpl; [ reflexivity | ].
  destruct (Pos.eqb k k'); [ reflexivity | exact IH ].
Qed.

(* An application whose continuation keeps all its parameters is not
   changed. *)
Lemma drop_args_none (known : masks) (ac : apply_cont) :
  mask_of known (ac_continuation ac) = None -> drop_args known ac = ac.
Proof.
  intros Hnone. unfold drop_args. rewrite Hnone. destruct ac. reflexivity.
Qed.

Lemma map_drop_args_none (known : masks) (arms : list (Z * apply_cont)) :
  (∀ k : continuation, mask_of known k = None) ->
  map (fun arm => (fst arm, drop_args known (snd arm))) arms = arms.
Proof.
  intros Hnone.
  induction arms as [ | [i ac] arms IH]; simpl; [ reflexivity | ].
  rewrite (drop_args_none known ac (Hnone _)), IH. reflexivity.
Qed.

Lemma find_arm_drop_args (known : masks) (i : Z)
    (arms : list (Z * apply_cont)) :
  find_arm i (map (fun arm => (fst arm, drop_args known (snd arm))) arms)
  = option_map (drop_args known) (find_arm i arms).
Proof.
  induction arms as [ | [discriminant ac] arms IH]; simpl; [ reflexivity | ].
  destruct (Z.eqb i discriminant); [ reflexivity | exact IH ].
Qed.

(* ======================================================================== *)
(* Evaluation under environments that agree                                 *)
(* ======================================================================== *)

Lemma eval_simple_agree (vars vars' : env) (s : simple) :
  (∀ x : variable, var_free_in_simple x s -> lookup x vars = lookup x vars') ->
  eval_simple vars' s = eval_simple vars s.
Proof.
  intros Hagree. destruct s as [x | sym | c]; simpl; try reflexivity.
  symmetry. apply Hagree. reflexivity.
Qed.

Lemma eval_simples_agree (vars vars' : env) (args : list simple) :
  (∀ x : variable, var_free_in_simples x args -> lookup x vars = lookup x vars')
  ->
  eval_simples vars' args = eval_simples vars args.
Proof.
  unfold var_free_in_simples.
  induction args as [ | s args IH]; intros Hagree; simpl; [ reflexivity | ].
  rewrite (eval_simple_agree vars vars' s), IH; [ reflexivity | | ].
  - intros x Hx. apply Hagree, Exists_cons_tl, Hx.
  - intros x Hx. apply Hagree, Exists_cons_hd, Hx.
Qed.

(* The arguments kept, under variables that agree on them, have the
   values kept. *)
Lemma eval_simples_keep (mask : list bool) :
  ∀ (args : list simple) (vars vars' : env) (vs : list value),
    eval_simples vars args = Some vs ->
    (∀ x : variable,
      var_free_in_simples x (keep mask args) -> lookup x vars = lookup x vars')
    ->
    eval_simples vars' (keep mask args) = Some (keep mask vs).
Proof.
  unfold var_free_in_simples.
  induction mask as [ | b mask IH]; intros args vars vars' vs Hargs Hagree;
    [ reflexivity | ].
  destruct args as [ | s args]; simpl in Hargs.
  - injection Hargs as <-. destruct b; reflexivity.
  - destruct (eval_simple vars s) as [v | ] eqn:Hs; [ | discriminate ].
    destruct (eval_simples vars args) as [rest | ] eqn:Hrest;
      [ | discriminate ].
    injection Hargs as <-. destruct b; simpl in Hagree |- *.
    + rewrite (eval_simple_agree vars vars' s), Hs,
        (IH args vars vars' rest Hrest);
        [ reflexivity | | ].
      * intros x Hx. apply Hagree, Exists_cons_tl, Hx.
      * intros x Hx. apply Hagree, Exists_cons_hd, Hx.
    + exact (IH args vars vars' rest Hrest Hagree).
Qed.

Lemma eval_simples_masked (mask : option (list bool)) (args : list simple)
    (vars vars' : env) (vs : list value) :
  eval_simples vars args = Some vs ->
  (∀ x : variable,
    var_free_in_simples x (keep_all_or mask args) ->
    lookup x vars = lookup x vars') ->
  eval_simples vars' (keep_all_or mask args) = Some (keep_all_or mask vs).
Proof.
  destruct mask as [mask | ]; simpl; intros Hargs Hagree.
  - exact (eval_simples_keep mask args vars vars' vs Hargs Hagree).
  - rewrite (eval_simples_agree vars vars' args Hagree). exact Hargs.
Qed.

Lemma eval_named_agree (statics : static_env) (vars vars' : env) (d : named) :
  (∀ x : variable, var_free_in_named x d -> lookup x vars = lookup x vars') ->
  eval_named statics vars' d = eval_named statics vars d.
Proof.
  intros Hagree. symmetry.
  apply (eval_named_match [] vars vars' statics statics d d);
    [ | apply statics_match_same | apply named_eqb_refl, reflexive_map_nil ].
  intros x x' Hx Hmatch. apply names_match_nil in Hmatch. subst x'.
  apply Hagree, Hx.
Qed.

Lemma eval_static_bindings_agree (vars vars' : env)
    (bindings : list static_binding) :
  (∀ x : variable,
    Exists (var_free_in_static_binding x) bindings ->
    lookup x vars = lookup x vars') ->
  ∀ statics : static_env,
    eval_static_bindings vars' bindings statics
    = eval_static_bindings vars bindings statics.
Proof.
  induction bindings as [ | [id c | id | s const] bindings IH];
    intros Hagree statics; simpl; [ reflexivity | | | ].
  - destruct (lookup id (static_code statics)); [ reflexivity | ].
    apply IH. intros x Hx. apply Hagree, Exists_cons_tl, Hx.
  - apply IH. intros x Hx. apply Hagree, Exists_cons_tl, Hx.
  - destruct (lookup s (static_values statics)); [ reflexivity | ].
    rewrite <- (eval_static_const_match [] vars vars' const const);
      [ | | apply static_const_eqb_refl, reflexive_map_nil ].
    + destruct (eval_static_const vars const); [ | reflexivity ].
      apply IH. intros x Hx. apply Hagree, Exists_cons_tl, Hx.
    + intros x x' Hx Hmatch. apply names_match_nil in Hmatch. subst x'.
      apply Hagree, Exists_cons_hd, Hx.
Qed.

(* ======================================================================== *)
(* Binding the parameters kept                                              *)
(* ======================================================================== *)

(* Binding the parameters kept to the values kept succeeds where binding
   them all does, and the two results agree on a variable that is not a
   parameter removed, if it is a parameter kept or the environments
   agreed on it. *)
Lemma bind_params_keep (params : list variable) :
  ∀ (mask : list bool) (vs : list value) (vars vars' bound : env),
    length mask = length params ->
    bind_params params vs vars = Some bound ->
    ∃ bound' : env,
      bind_params (keep mask params) (keep mask vs) vars' = Some bound'
      ∧ ∀ x : variable,
          x ∉ dropped mask params ->
          x ∈ keep mask params ∨ lookup x vars = lookup x vars' ->
          lookup x bound = lookup x bound'.
Proof.
  induction params as [ | p params IH];
    intros mask vs vars vars' bound Hlen Hbind.
  - destruct mask; [ | discriminate Hlen ].
    destruct vs; [ | discriminate Hbind ].
    injection Hbind as <-. exists vars'. split; [ reflexivity | ].
    intros x _ [[] | Hx]. exact Hx.
  - destruct mask as [ | b mask]; [ discriminate Hlen | ].
    destruct vs as [ | v vs]; [ discriminate Hbind | ].
    simpl in Hlen, Hbind. injection Hlen as Hlen.
    destruct b; unfold dropped; simpl.
    + destruct (IH mask vs ((p, v) :: vars) ((p, v) :: vars') bound Hlen Hbind)
        as (bound' & Hbind' & Hagree).
      exists bound'. split; [ exact Hbind' | ].
      intros x Hdropped Hx. apply Hagree; [ exact Hdropped | ]. simpl.
      destruct (Pos.eqb_spec x p) as [-> | Hne]; [ right; reflexivity | ].
      destruct Hx as [[Heq | Hin] | Hlookup];
        [ congruence | left; exact Hin | right; exact Hlookup ].
    + destruct (IH mask vs ((p, v) :: vars) vars' bound Hlen Hbind)
        as (bound' & Hbind' & Hagree).
      exists bound'. split; [ exact Hbind' | ].
      intros x Hdropped Hx. apply Hagree.
      * intros Hin. apply Hdropped. right. exact Hin.
      * simpl. destruct (Pos.eqb_spec x p) as [-> | Hne]; [ | exact Hx ].
        exfalso. apply Hdropped. left. reflexivity.
Qed.

(* The same for a mask that may keep everything, and a handler it fits:
   the two results agree on the free variables of the handler, if the
   environments agreed on those of the handler with its parameters. *)
Lemma bind_params_masked (mask : option (list bool))
    (params : list variable) (metadata' : handler_metadata) (handler' : expr)
    (vs : list value) (vars vars' bound : env) :
  mask_fits mask params handler' ->
  bind_params params vs vars = Some bound ->
  (∀ x : variable,
    var_free_in_handler x
      (Handler (keep_all_or mask params) metadata' handler') ->
    lookup x vars = lookup x vars') ->
  ∃ bound' : env,
    bind_params (keep_all_or mask params) (keep_all_or mask vs) vars'
    = Some bound'
    ∧ ∀ x : variable,
        var_free_in_expr x handler' -> lookup x bound = lookup x bound'.
Proof.
  intros Hfits Hbind Hvars. destruct mask as [mask | ]; simpl in *.
  - destruct Hfits as [Hlen Hdropped].
    destruct (bind_params_keep params mask vs vars vars' bound Hlen Hbind)
      as (bound' & Hbind' & Hagree).
    exists bound'. split; [ exact Hbind' | ].
    intros x Hx. apply Hagree.
    + intros Hin. exact (Hdropped x Hin Hx).
    + destruct (in_dec Pos.eq_dec x (keep mask params)) as [Hin | Hnotin];
        [ left; exact Hin | right; apply Hvars; split; assumption ].
  - destruct (bind_params_defined params vs vars vars' bound Hbind)
      as [bound' Hbind'].
    exists bound'. split; [ exact Hbind' | ].
    intros x Hx. symmetry.
    apply (bind_params_agree params vs vars vars' bound bound' Hbind Hbind').
    destruct (in_dec Pos.eq_dec x params) as [Hin | Hnotin];
      [ left; exact Hin | right; symmetry; apply Hvars; split; assumption ].
Qed.

(* The values kept are of the kinds kept. *)
Lemma map_keep {A B : Type} (g : A -> B) (mask : list bool) :
  ∀ l : list A, map g (keep mask l) = keep mask (map g l).
Proof.
  induction mask as [ | b mask IH]; intros [ | a l]; simpl; try reflexivity.
  - destruct b; reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma kinds_masked (mask : option (list bool)) (vs : list value)
    (kinds kinds' : list flambda_kind) :
  kinds' = keep_all_or mask kinds ->
  kinds_eqb (map kind_of_value vs) kinds = true ->
  kinds_eqb (map kind_of_value (keep_all_or mask vs)) kinds' = true.
Proof.
  intros -> Hkinds. apply kinds_eqb_eq in Hkinds. subst kinds.
  apply kinds_eqb_eq. destruct mask as [mask | ]; simpl;
    [ apply map_keep | reflexivity ].
Qed.

(* The kinds that [keep_kinds] leaves. *)
Lemma keep_kinds_kinds (mask : option (list bool))
    (metadata : handler_metadata) :
  hm_params_kinds (keep_kinds mask metadata)
  = keep_all_or mask (hm_params_kinds metadata).
Proof.
  destruct mask as [mask | ]; simpl; [ | reflexivity ].
  destruct (hm_is_exn_handler metadata); reflexivity.
Qed.

(* ======================================================================== *)
(* An expression with parameters and arguments removed                      *)
(* ======================================================================== *)

Definition handler_params (h : continuation_handler) : list variable :=
  match h with
  | Handler params _ _ => params
  end.

Definition handler_kinds (h : continuation_handler) : list flambda_kind :=
  match h with
  | Handler _ metadata _ => hm_params_kinds metadata
  end.

Definition handler_expr (h : continuation_handler) : expr :=
  match h with
  | Handler _ _ handler => handler
  end.

(* The second expression is the first with, at each non-recursive
   [Let_cont], some parameters removed that the second handler does not
   use, their kinds removed with them, and their arguments removed where
   the continuation is applied. The handlers of a recursive [Let_cont]
   give the same kinds. No [Apply] returns to a continuation that has
   lost a parameter. (The
   warning silenced is about induction schemes, which nothing uses.) *)
#[local] Set Warnings "-register-all".
Inductive drops : masks -> expr -> expr -> Prop :=
  | Drops_let (known : masks) (x : variable) (kind : flambda_kind)
      (d : named) (body body' : expr) :
    drops known body body' ->
    drops known (Let x kind d body) (Let x kind d body')
  | Drops_let_static (known : masks) (bindings : list static_binding)
      (body body' : expr) :
    drops known body body' ->
    drops known (Let_static bindings body) (Let_static bindings body')
  | Drops_let_cont (known : masks) (k : continuation)
      (params : list variable) (metadata metadata' : handler_metadata)
      (handler handler' : expr) (mask : option (list bool))
      (body body' : expr) :
    drops known handler handler' ->
    mask_fits mask params handler' ->
    hm_params_kinds metadata' = keep_all_or mask (hm_params_kinds metadata) ->
    drops ((k, mask) :: known) body body' ->
    drops known
      (Let_cont_non_recursive k (Handler params metadata handler) body)
      (Let_cont_non_recursive k
         (Handler (keep_all_or mask params) metadata' handler') body')
  | Drops_let_cont_recursive (known : masks)
      (handlers handlers' : list (continuation * continuation_handler))
      (body body' : expr) :
    Forall2
      (fun kh kh' =>
         fst kh = fst kh'
         ∧ handler_params (snd kh) = handler_params (snd kh')
         ∧ handler_kinds (snd kh) = handler_kinds (snd kh')
         ∧ drops (rec_masks handlers ++ known) (handler_expr (snd kh))
             (handler_expr (snd kh')))
      handlers handlers' ->
    handlers_bind_statics handlers' = handlers_bind_statics handlers ->
    drops (rec_masks handlers ++ known) body body' ->
    drops known (Let_cont_recursive handlers body)
      (Let_cont_recursive handlers' body')
  | Drops_apply (known : masks) (ap : apply_expr) :
    mask_of known (ap_continuation ap) = None ->
    mask_of known (ap_exn_continuation ap) = None ->
    drops known (Apply ap) (Apply ap)
  | Drops_apply_cont (known : masks) (ac : apply_cont) :
    drops known (Apply_cont ac) (Apply_cont (drop_args known ac))
  | Drops_switch (known : masks) (scrutinee : simple)
      (arms : list (Z * apply_cont)) :
    drops known (Switch scrutinee arms)
      (Switch scrutinee
         (map (fun arm => (fst arm, drop_args known (snd arm))) arms))
  | Drops_invalid (known : masks) : drops known Invalid Invalid.

(* The handlers of a recursive [Let_cont], one with one: the same names,
   parameters and kinds, and expressions so related. *)
Definition handlers_drop (known : masks)
    (handlers handlers' : list (continuation * continuation_handler)) : Prop :=
  Forall2
    (fun kh kh' =>
       fst kh = fst kh'
       ∧ handler_params (snd kh) = handler_params (snd kh')
       ∧ handler_kinds (snd kh) = handler_kinds (snd kh')
       ∧ drops known (handler_expr (snd kh)) (handler_expr (snd kh')))
    handlers handlers'.

Lemma handlers_drop_lookup (known : masks) (k : continuation)
    (handlers handlers' : list (continuation * continuation_handler)) :
  handlers_drop known handlers handlers' ->
  match lookup k handlers, lookup k handlers' with
  | Some h, Some h' =>
    handler_params h = handler_params h'
    ∧ handler_kinds h = handler_kinds h'
    ∧ drops known (handler_expr h) (handler_expr h')
  | None, None => True
  | _, _ => False
  end.
Proof.
  induction 1 as [ | [k1 h] [k1' h'] handlers handlers' (Hk & Hh) _ IH];
    simpl; [ exact I | ].
  simpl in Hk, Hh. subst k1'. destruct (Pos.eqb k k1); [ exact Hh | exact IH ].
Qed.

(* Every expression is related to itself, with every parameter kept. *)
Fixpoint drops_refl (e : expr) :
  ∀ known : masks,
    (∀ k : continuation, mask_of known k = None) -> drops known e e.
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros known Hnone.
  - apply Drops_let, drops_refl, Hnone.
  - apply Drops_let_static, drops_refl, Hnone.
  - apply (Drops_let_cont known k params metadata metadata handler handler
      None body body);
      [ apply drops_refl, Hnone | exact I | reflexivity | apply drops_refl ].
    intros k1. destruct (Pos.eq_dec k1 k) as [-> | Hne];
      [ apply mask_of_head | rewrite mask_of_other by exact Hne; apply Hnone ].
  - assert (Hnone' :
      ∀ k : continuation, mask_of (rec_masks handlers ++ known) k = None).
    { intros k. rewrite mask_of_rec_masks.
      destruct (lookup k handlers); [ reflexivity | apply Hnone ]. }
    apply Drops_let_cont_recursive;
      [ | reflexivity | apply drops_refl, Hnone' ].
    revert Hnone'. generalize (rec_masks handlers ++ known).
    intros known' Hnone'.
    induction handlers as [ | [k [params metadata handler]] handlers IH];
      [ apply Forall2_nil | ].
    apply Forall2_cons; [ | exact IH ].
    simpl. split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ reflexivity | ].
    apply drops_refl, Hnone'.
  - apply Drops_apply; apply Hnone.
  - pose proof (Drops_apply_cont known ac) as Hdrops.
    rewrite (drop_args_none known ac (Hnone _)) in Hdrops. exact Hdrops.
  - pose proof (Drops_switch known scrutinee arms) as Hdrops.
    rewrite (map_drop_args_none known arms Hnone) in Hdrops. exact Hdrops.
  - apply Drops_invalid.
Qed.

(* ======================================================================== *)
(* The pass relates a term to its result                                    *)
(* ======================================================================== *)

(* No [Apply] of the expression returns to a continuation that the masks
   take a parameter from. *)
Definition safe (known : masks) (e : expr) : Prop :=
  ∀ (k : continuation) (mask : list bool),
    mask_of known k = Some mask -> returned_to k e = false.

Fixpoint drop_params_binds_statics (e : expr) :
  ∀ known : masks, binds_statics (drop_params known e) = binds_statics e.
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros known; simpl; try reflexivity.
  - apply drop_params_binds_statics.
  - rewrite drop_params_binds_statics. reflexivity.
  - rewrite !drop_params_binds_statics. reflexivity.
  - rewrite drop_params_binds_statics. f_equal.
    generalize (map (fun '(k, _) => (k, @None (list bool))) handlers ++ known).
    intros known'.
    induction handlers as [ | [k [params metadata handler]] handlers IH];
      simpl; [ reflexivity | ].
    rewrite drop_params_binds_statics, IH. reflexivity.
Qed.

(* The parameters that [used_params] removes are not free in the
   handler. *)
Lemma dropped_unused (handler : expr) (params : list variable)
    (x : variable) :
  x ∈ dropped (map (fun param => var_free_b param handler) params) params ->
  var_free_b x handler = false.
Proof.
  unfold dropped.
  induction params as [ | p params IH]; simpl; [ intros [] | ].
  destruct (var_free_b p handler) eqn:Hp; simpl; [ exact IH | ].
  intros [<- | Hin]; [ exact Hp | exact (IH Hin) ].
Qed.

(* The mask with the first parameter of an exception handler kept. *)
Definition exn_bucket_kept (is_exn_handler : bool) (mask : list bool)
    : list bool :=
  match is_exn_handler, mask with
  | true, _ :: mask => true :: mask
  | _, _ => mask
  end.

Lemma exn_bucket_kept_length (is_exn_handler : bool) (mask : list bool) :
  length (exn_bucket_kept is_exn_handler mask) = length mask.
Proof. destruct is_exn_handler, mask; reflexivity. Qed.

(* Keeping it removes no more. *)
Lemma dropped_exn_bucket_kept {A : Type} (is_exn_handler : bool)
    (mask : list bool) (l : list A) (a : A) :
  a ∈ dropped (exn_bucket_kept is_exn_handler mask) l -> a ∈ dropped mask l.
Proof.
  destruct is_exn_handler; [ | exact (fun Hin => Hin) ].
  destruct mask as [ | b mask]; [ exact (fun Hin => Hin) | ].
  destruct l as [ | a' l]; [ destruct b; exact (fun Hin => Hin) | ].
  unfold dropped. simpl. destruct b; simpl; [ exact (fun Hin => Hin) | ].
  intros Hin. right. exact Hin.
Qed.

Lemma used_params_fit (is_exn_handler : bool) (params : list variable)
    (handler : expr) :
  mask_fits (used_params is_exn_handler params handler) params handler.
Proof.
  unfold used_params.
  change
    (match is_exn_handler, map (fun param => var_free_b param handler) params
     with
     | true, _ :: mask => true :: mask
     | _, _ => map (fun param => var_free_b param handler) params
     end)
    with
      (exn_bucket_kept is_exn_handler
         (map (fun param => var_free_b param handler) params)).
  destruct
    (forallb (fun used => used)
       (exn_bucket_kept is_exn_handler
          (map (fun param => var_free_b param handler) params)));
    [ exact I | ].
  split; [ rewrite exn_bucket_kept_length; apply length_map | ].
  intros x Hin Hfree. apply dropped_exn_bucket_kept, dropped_unused in Hin.
  apply var_free_b_sound in Hfree. congruence.
Qed.

Fixpoint drop_params_drops (e : expr) :
  ∀ known : masks, safe known e -> drops known e (drop_params known e).
Proof.
  destruct e
    as [ x kind d body | bindings body | k [params metadata handler] body
       | handlers body | ap | ac | scrutinee arms | ];
    intros known Hsafe; simpl.
  - apply Drops_let, drop_params_drops. exact Hsafe.
  - apply Drops_let_static, drop_params_drops. exact Hsafe.
  - apply Drops_let_cont.
    + apply drop_params_drops. intros k1 mask Hmask.
      specialize (Hsafe k1 mask Hmask). simpl in Hsafe.
      apply orb_false_iff in Hsafe as [Hhandler _]. exact Hhandler.
    + destruct (returned_to k body); [ exact I | apply used_params_fit ].
    + apply keep_kinds_kinds.
    + apply drop_params_drops. intros k1 mask Hmask.
      destruct (Pos.eq_dec k1 k) as [-> | Hne].
      * rewrite mask_of_head in Hmask.
        destruct (returned_to k body); [ discriminate Hmask | reflexivity ].
      * rewrite mask_of_other in Hmask by exact Hne.
        specialize (Hsafe k1 mask Hmask). simpl in Hsafe.
        apply orb_false_iff in Hsafe as [_ Hbody]. exact Hbody.
  - change (map (fun '(k, _) => (k, @None (list bool))) handlers)
      with (rec_masks handlers).
    assert (Hsafe' :
      ∀ (k : continuation) (mask : list bool),
        mask_of (rec_masks handlers ++ known) k = Some mask ->
        existsb (fun '(_, h) => returned_to_in_handler k h) handlers = false
        ∧ returned_to k body = false).
    { intros k mask. rewrite mask_of_rec_masks.
      destruct (lookup k handlers); [ discriminate | ].
      intros Hmask. specialize (Hsafe k mask Hmask). simpl in Hsafe.
      apply orb_false_iff in Hsafe. exact Hsafe. }
    apply Drops_let_cont_recursive.
    + clear Hsafe. revert Hsafe'. generalize (rec_masks handlers ++ known).
      intros known' Hsafe'.
      induction handlers as [ | [k [params metadata handler]] handlers IH];
        [ apply Forall2_nil | ].
      apply Forall2_cons.
      * simpl. split; [ reflexivity | ]. split; [ reflexivity | ].
        split; [ reflexivity | ].
        apply drop_params_drops. intros k1 mask Hmask.
        destruct (Hsafe' k1 mask Hmask) as [Hhandlers _]. simpl in Hhandlers.
        apply orb_false_iff in Hhandlers as [Hhandler _]. exact Hhandler.
      * apply IH. intros k1 mask Hmask.
        destruct (Hsafe' k1 mask Hmask) as [Hhandlers Hbody].
        simpl in Hhandlers.
        apply orb_false_iff in Hhandlers as [_ Hrest].
        exact (conj Hrest Hbody).
    + clear Hsafe Hsafe'. unfold handlers_bind_statics.
      generalize (rec_masks handlers ++ known). intros known'.
      induction handlers as [ | [k [params metadata handler]] handlers IH];
        simpl; [ reflexivity | ].
      rewrite drop_params_binds_statics, IH. reflexivity.
    + apply drop_params_drops. intros k mask Hmask.
      exact (proj2 (Hsafe' k mask Hmask)).
  - apply Drops_apply.
    + destruct (mask_of known (ap_continuation ap)) as [mask | ] eqn:Hmask;
        [ | reflexivity ].
      specialize (Hsafe _ mask Hmask). simpl in Hsafe.
      rewrite Pos.eqb_refl in Hsafe. discriminate Hsafe.
    + destruct (mask_of known (ap_exn_continuation ap)) as [mask | ]
        eqn:Hmask; [ | reflexivity ].
      specialize (Hsafe _ mask Hmask). simpl in Hsafe.
      rewrite Pos.eqb_refl, orb_true_r in Hsafe. discriminate Hsafe.
  - apply Drops_apply_cont.
  - apply Drops_switch.
  - apply Drops_invalid.
Qed.

(* ======================================================================== *)
(* Continuations and states                                                 *)
(* ======================================================================== *)

(* What a continuation name stands for in the two runs, given the mask
   of the name: the same thing, if all its parameters are kept; or
   closures whose handlers are related under the masks of where they
   were defined, the second with the parameters that the mask keeps and
   their kinds, under variables that agree on the free variables of the second
   handler and of the handlers defined with it, and under continuations
   that are in turn so related; or two that are related with all their
   parameters kept, with the same extra arguments. *)
Inductive cont_drops : option (list bool) -> cont_value -> cont_value -> Prop :=
  | Same_drops (c : cont_value) : cont_drops None c c
  | Closure_drops (mask : option (list bool)) (known : masks)
      (params : list variable) (metadata metadata' : handler_metadata)
      (handler handler' : expr) (vars vars' : env) (conts conts' : cont_env)
      (recursive recursive' : list (continuation * continuation_handler)) :
    handlers_drop (rec_masks recursive ++ known) recursive recursive' ->
    drops (rec_masks recursive ++ known) handler handler' ->
    mask_fits mask params handler' ->
    hm_params_kinds metadata' = keep_all_or mask (hm_params_kinds metadata) ->
    (∀ x : variable,
      var_free_in_handler x
        (Handler (keep_all_or mask params) metadata' handler')
      ∨ any_handler (var_free_in_handler x) recursive' ->
      lookup x vars = lookup x vars') ->
    (∀ k : continuation,
      cont_drops (mask_of known k) (resolve k conts) (resolve k conts')) ->
    cont_drops mask
      (Closure (Handler params metadata handler) vars conts recursive)
      (Closure (Handler (keep_all_or mask params) metadata' handler') vars'
         conts' recursive')
  | Extra_args_drops (c c' : cont_value) (extra : list value) :
    cont_drops None c c' ->
    cont_drops None (Extra_args c extra) (Extra_args c' extra).

Lemma with_extra_args_drops (c c' : cont_value) (extra : list value) :
  cont_drops None c c' ->
  cont_drops None (with_extra_args c extra) (with_extra_args c' extra).
Proof.
  intros Hc. destruct extra; simpl; [ exact Hc | apply Extra_args_drops, Hc ].
Qed.

Definition conts_drop (known : masks) (conts conts' : cont_env) : Prop :=
  ∀ k : continuation,
    cont_drops (mask_of known k) (resolve k conts) (resolve k conts').

Inductive state_drops : state -> state -> Prop :=
  | State_drops (known : masks) (e e' : expr) (vars vars' : env)
      (conts conts' : cont_env) (statics : static_env) :
    drops known e e' ->
    (∀ x : variable, var_free_in_expr x e' -> lookup x vars = lookup x vars') ->
    conts_drop known conts conts' ->
    state_drops (State e vars conts statics) (State e' vars' conts' statics).

Lemma state_drops_refl (s : state) : state_drops s s.
Proof.
  destruct s as [e vars conts statics].
  apply (State_drops []);
    [ apply drops_refl; reflexivity | reflexivity
    | intros k; apply Same_drops ].
Qed.

(* The closures of the handlers of a recursive [Let_cont], over
   continuations that are related. *)
Lemma rec_conts_drop (known : masks)
    (handlers handlers' : list (continuation * continuation_handler))
    (vars vars' : env) (conts conts' : cont_env) :
  handlers_drop (rec_masks handlers ++ known) handlers handlers' ->
  (∀ x : variable,
    any_handler (var_free_in_handler x) handlers' ->
    lookup x vars = lookup x vars') ->
  conts_drop known conts conts' ->
  conts_drop (rec_masks handlers ++ known)
    (rec_closures handlers vars conts ++ conts)
    (rec_closures handlers' vars' conts' ++ conts').
Proof.
  intros Hhandlers Hvars Hconts k.
  rewrite mask_of_rec_masks, !resolve_rec_closures.
  pose proof (handlers_drop_lookup _ k _ _ Hhandlers) as Hlookup.
  destruct (lookup k handlers) as [[params metadata handler] | ],
    (lookup k handlers') as [[params' metadata' handler'] | ] eqn:Hl';
    try contradiction; [ | apply Hconts ].
  destruct Hlookup as (Hparams & Hkinds & Hhandler).
  simpl in Hparams, Hkinds, Hhandler. subst params'.
  apply (Closure_drops None known params metadata metadata' handler handler'
    vars vars' conts conts' handlers handlers');
    [ exact Hhandlers | exact Hhandler | exact I | symmetry; exact Hkinds |
    | exact Hconts ].
  intros x [Hx | Hx]; apply Hvars; [ | exact Hx ].
  exact (any_handler_in _ k _ _ (lookup_in _ _ _ Hl') Hx).
Qed.

(* ======================================================================== *)
(* The simulation                                                           *)
(* ======================================================================== *)

Lemma drops_step (s s' : state) :
  state_drops s s' -> result_simulated state_drops (step s) (step s').
Proof.
  intros [known e e' vars vars' conts conts' statics Hdrops Hvars Hconts].
  destruct Hdrops
    as [ known x kind d body body' Hbody | known bindings body body' Hbody
       | known k params metadata metadata' handler handler' mask body body'
           Hhandler Hfits Hkinds Hbody
       | known handlers handlers' body body' Hhandlers Hbinds Hbody
       | known ap Hret Hexn | known ac | known scrutinee arms | known ];
    autorewrite with step.
  - (* Let *)
    rewrite (eval_named_agree statics vars vars' d)
      by (intros y Hy; apply Hvars; left; exact Hy).
    destruct (eval_named statics vars d) as [v | ]; simpl; [ | exact I ].
    destruct (kind_eqb (kind_of_value v) kind); simpl; [ | exact I ].
    apply (State_drops known); [ exact Hbody | | exact Hconts ].
    intros y Hy. simpl.
    destruct (Pos.eqb_spec y x) as [-> | Hne]; [ reflexivity | ].
    apply Hvars. right. split; assumption.
  - (* Let_static *)
    rewrite (eval_static_bindings_agree vars vars' bindings)
      by (intros y Hy; apply Hvars; left; exact Hy).
    destruct (eval_static_bindings vars bindings statics) as [extended | ];
      simpl; [ | exact I ].
    apply (State_drops known); [ exact Hbody | | exact Hconts ].
    intros y Hy. apply Hvars. right. exact Hy.
  - (* Let_cont_non_recursive *)
    simpl. apply (State_drops ((k, mask) :: known)); [ exact Hbody | | ].
    + intros y Hy. apply Hvars. right. exact Hy.
    + intros k'. destruct (Pos.eq_dec k' k) as [-> | Hne].
      * rewrite mask_of_head, !resolve_head.
        apply (Closure_drops mask known params metadata metadata' handler
          handler' vars vars' conts conts' [] []);
          [ apply Forall2_nil | exact Hhandler | exact Hfits | exact Hkinds |
          | exact Hconts ].
        intros y [Hy | []]. apply Hvars. left. exact Hy.
      * rewrite mask_of_other, !resolve_other by exact Hne. apply Hconts.
  - (* Let_cont_recursive *)
    rewrite Hbinds.
    destruct (handlers_bind_statics handlers); simpl; [ exact I | ].
    apply (State_drops (rec_masks handlers ++ known)); [ exact Hbody | | ].
    + intros y Hy. apply Hvars. right. exact Hy.
    + apply rec_conts_drop; [ exact Hhandlers | | exact Hconts ].
      intros y Hy. apply Hvars. left. exact Hy.
  - (* Apply: the same call, returning to related continuations *)
    rewrite (eval_simple_agree vars vars' (ap_callee ap))
      by (intros y Hy; apply Hvars; left; exact Hy).
    rewrite (eval_simples_agree vars vars' (ap_args ap))
      by (intros y Hy; apply Hvars; right; left; exact Hy).
    rewrite (eval_simples_agree vars vars' (exn_extra_simples ap))
      by (intros y Hy; apply Hvars; right; right; exact Hy).
    destruct (eval_simple vars (ap_callee ap)) as [callee | ]; [ | exact I ].
    destruct (eval_simples vars (ap_args ap)) as [vs | ]; [ | exact I ].
    destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ];
      [ | exact I ].
    destruct (call_function_cases callee (ap_call_kind ap) vs
                (ap_args_arity ap) (ap_return_arity ap) statics)
      as [Hundefined | (body & callee_vars & ret & exn & Hcall)].
    + rewrite !Hundefined. exact I.
    + rewrite !Hcall. simpl.
      apply (State_drops []);
        [ apply drops_refl; reflexivity | reflexivity | ].
      intros k'. pose proof (Hconts (ap_continuation ap)) as Hreturn.
      pose proof (Hconts (ap_exn_continuation ap)) as Hraise.
      rewrite Hret in Hreturn. rewrite Hexn in Hraise.
      destruct (Pos.eq_dec k' ret) as [-> | Hne];
        [ rewrite !resolve_head; exact Hreturn | ].
      rewrite !(resolve_other k' ret) by exact Hne.
      destruct (Pos.eq_dec k' exn) as [-> | Hne'];
        [ rewrite !resolve_head; apply with_extra_args_drops, Hraise | ].
      rewrite !(resolve_other k' exn) by exact Hne'. apply Same_drops.
  - (* Apply_cont *)
    unfold drop_args. cbn [ac_args ac_continuation].
    destruct (eval_simples vars (ac_args ac)) as [vs | ] eqn:Hargs;
      [ | exact I ].
    rewrite (eval_simples_masked _ _ vars vars' vs Hargs)
      by (intros y Hy; apply Hvars; exact Hy).
    unfold apply_continuation.
    pose proof (Hconts (ac_continuation ac)) as Hc.
    remember (mask_of known (ac_continuation ac)) as mask eqn:Hmask.
    remember (resolve (ac_continuation ac) conts) as c eqn:Hresolve.
    remember (resolve (ac_continuation ac) conts') as c' eqn:Hresolve'.
    clear Hmask Hresolve Hresolve' Hargs. revert vs.
    induction Hc
      as [c
         | mask known' params metadata metadata' handler handler' def_vars
             def_vars' def_conts def_conts' recursive recursive' Hrecursive
             Hhandler Hfits Hkinds Hdef_vars Hdef_conts _
         | c c' extra Hc IHc];
      intros vs.
    + (* the same continuation *)
      simpl.
      destruct (apply_cont_value c vs statics) as [s1 | k1 vs1 | ]; simpl;
        [ apply state_drops_refl | auto | exact I ].
    + (* related closures *)
      simpl.
      destruct (kinds_eqb (map kind_of_value vs) (hm_params_kinds metadata))
        eqn:Hgiven; [ | exact I ].
      rewrite (kinds_masked mask vs _ _ Hkinds Hgiven).
      destruct (bind_params params vs def_vars) as [bound | ] eqn:Hbind;
        [ | exact I ].
      destruct (bind_params_masked mask params metadata' handler' vs def_vars
                  def_vars' bound Hfits Hbind)
        as (bound' & Hbind' & Hagree);
        [ intros y Hy; apply Hdef_vars; left; exact Hy | ].
      rewrite Hbind'. simpl.
      apply (State_drops (rec_masks recursive ++ known'));
        [ exact Hhandler | exact Hagree | ].
      apply rec_conts_drop; [ exact Hrecursive | | exact Hdef_conts ].
      intros y Hy. apply Hdef_vars. right. exact Hy.
    + (* the same extra arguments *)
      exact (IHc (vs ++ extra)).
  - (* Switch *)
    rewrite (eval_simple_agree vars vars' scrutinee)
      by (intros y Hy; apply Hvars; left; exact Hy).
    destruct (eval_simple vars scrutinee) as [v | ]; [ | exact I ].
    destruct (naked_immediate_of_value v) as [i | ]; [ | exact I ].
    rewrite find_arm_drop_args.
    destruct (find_arm i arms) as [ac | ] eqn:Hfind; simpl; [ | exact I ].
    apply (State_drops known); [ apply Drops_apply_cont | | exact Hconts ].
    intros y Hy. apply Hvars. right. apply Exists_exists.
    exists (i, drop_args known ac). split; [ | exact Hy ].
    apply in_map_iff. exists (i, ac).
    split; [ reflexivity | apply find_arm_in, Hfind ].
  - (* Invalid *)
    exact I.
Qed.

Theorem drop_unused_params_refines : drop_unused_params_refines_statement.
Proof.
  intros e vars conts statics.
  apply (simulation_refines state_drops drops_step).
  apply (State_drops []);
    [ apply drop_params_drops; intros k mask Hmask; discriminate Hmask
    | reflexivity | intros k; apply Same_drops ].
Qed.
