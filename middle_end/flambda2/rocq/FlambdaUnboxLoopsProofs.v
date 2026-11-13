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


(* Proofs of the statement of FlambdaUnboxLoopsSpec.v. Nothing here
   needs review.

   One read made a parameter is two refinements
   ([unbox_loop_read_refines]). The first takes the read to the head
   of the handler ([hoisted_refines]): the handler without the [Let],
   entered with its variable bound to what the primitive has on the
   parameter read, refines the handler
   (FlambdaUnboxParamsProofs.read_refines), and where the primitive
   has no value of the kind of the [Let] the handler goes wrong, as
   the read is under [Let]s only ([spine_read_wrong]); a recursive
   [Let_cont] refines the same with a handler that refines its own
   (FlambdaContextProofs.let_cont_recursive_handler_refines_at). The
   second is the simulation of FlambdaUnboxParamsProofs.v for a
   recursive continuation
   (FlambdaUnboxParamsProofs.unbox_loop_parameter_refines): what it
   asks is that the handler before, entered with the values of an
   application, comes in one step to what the handler after extends,
   with the new parameter bound to an argument that is as asked; here
   the step is the [Let] of the read, and what is known after it is
   what the applications in the handler were extended with. The pass
   is that, for the reads of each parameter in turn, and the
   traversal carries what is known as
   FlambdaUnboxVariantsProofs.unbox_variants_knowing_refines does. *)

From Stdlib Require Import ZArith List Bool Arith Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaKindModel FlambdaValueSpec FlambdaPrimitiveModel
  FlambdaPrimitiveSpec FlambdaPrimitiveProofs FlambdaSemanticsSpec
  FlambdaSemanticsProofs FlambdaContextProofs FlambdaWellFormedSpec
  FlambdaWellFormedProofs FlambdaNormaliseSpec FlambdaNormaliseProofs
  FlambdaBlockLoadSpec FlambdaUnboxSpec FlambdaUnboxParamsSpec
  FlambdaUnboxParamsProofs FlambdaUnboxVariantsSpec
  FlambdaUnboxVariantsProofs FlambdaUnboxInScopeSpec
  FlambdaUnboxInScopeProofs FlambdaUnboxLoopsSpec.
Import ListNotations.

(* ======================================================================== *)
(* A read on the spine, taken to the head of the handler                    *)
(* ======================================================================== *)

(* Removing a [Let] of a primitive changes no static binding. *)
Lemma removes_binds_statics (f : variable) (kind : flambda_kind)
    (p : unary_primitive) (x : variable) (e e' : expr) :
  removes f kind p x e e' -> binds_statics e' = binds_statics e.
Proof.
  intros Hremoves.
  induction Hremoves
    as [ rest | y kind0 d body body' _ _ _ IH
       | k params metadata handler handler' body _ _ _ IH
       | k h body body' _ IH ];
    simpl; try rewrite IH; reflexivity.
Qed.

(* Where the read is under [Let]s only and the primitive has no value
   of the kind of the [Let] on what the parameter read holds, the
   expression goes wrong: each [Let] above the read has a step or none,
   and the read has none. *)
Lemma spine_read_wrong (f : variable) (kind : flambda_kind)
    (p : unary_primitive) (x : variable) (v : value) (e e' : expr) :
  removes f kind p x e e' ->
  on_spine f e = true ->
  ∀ (vars : env) (conts : cont_env) (statics : static_env) (hp : heap),
    lookup x vars = Some v ->
    match eval_prim statics (Unary p) [v] with
    | Some w => kind_eqb (kind_of_value w) kind = false
    | None => True
    end ->
    behaves (State e vars conts statics hp) Goes_wrong.
Proof.
  intros Hremoves.
  induction Hremoves
    as [ rest | y kind0 d body body' Hx Hf _ IH
       | k params metadata handler handler' body _ _ _ _
       | k h body body' _ _ ];
    intros Hspine vars conts statics hp Hlookup Hwrong; simpl in Hspine;
    try discriminate.
  - apply step_undefined_wrong. rewrite step_let. simpl. rewrite Hlookup.
    simpl.
    destruct (eval_prim statics (Unary p) [v]) as [w | ];
      [ rewrite Hwrong | ]; reflexivity.
  - rewrite Hf in Hspine. simpl in Hspine.
    apply (step_behaves _ Goes_wrong). rewrite step_let.
    destruct (eval_named statics vars d) as [v0 | ]; [ | reflexivity ].
    destruct (kind_eqb (kind_of_value v0) kind0); [ | reflexivity ].
    simpl. apply IH; [ exact Hspine | | exact Hwrong ].
    rewrite lookup_other by (apply Pos.eqb_neq; exact Hx). exact Hlookup.
Qed.

(* The expression refines to the same with the read taken to its
   head. *)
Lemma hoisted_refines (f : variable) (kind : flambda_kind)
    (p : unary_primitive) (x : variable) (e e' : expr) (v : value)
    (bound : env) (conts : cont_env) (statics : static_env) (hp : heap) :
  removes f kind p x e e' ->
  on_spine f e = true ->
  var_free_b f e = false ->
  Pos.eqb x f = false ->
  lookup x bound = Some v ->
  refines (State e bound conts statics hp)
    (State (Let f kind (Prim (Unary p) [Var x]) e') bound conts statics hp).
Proof.
  intros Hremoves Hspine Hfree Hne Hlookup.
  pose proof (spine_read_wrong f kind p x v e e' Hremoves Hspine bound conts
    statics hp Hlookup) as Hwrong.
  destruct (eval_prim statics (Unary p) [v]) as [w | ] eqn:Hprim;
    [ | apply goes_wrong_refines, Hwrong; exact I ].
  destruct (kind_eqb (kind_of_value w) kind) eqn:Hkind;
    [ | apply goes_wrong_refines, Hwrong; reflexivity ].
  apply (refines_trans _ (State e' ((f, w) :: bound) conts statics hp)).
  - apply (read_refines f kind p x v w e e' bound conts statics hp Hremoves
      Hfree Hne Hlookup).
    intros statics' [_ Hvalues] w' Hprim'.
    rewrite
      (eval_prim_statics_extend statics statics' _ [v] w
         (fun s allocated _ Hs => Hvalues s allocated Hs) Hprim)
      in Hprim'.
    congruence.
  - apply equivalent_refines, equivalent_sym, step_equivalent.
    rewrite step_let. simpl. rewrite Hlookup. simpl. rewrite Hprim, Hkind.
    reflexivity.
Qed.

(* ======================================================================== *)
(* One read of a loop made a parameter                                      *)
(* ======================================================================== *)

Lemma nth_error_among (x : variable) (xs : list variable) (i : nat) :
  nth_error xs i = Some x -> among x xs = true.
Proof. intros Hnth. apply among_In. exact (nth_error_In xs i Hnth). Qed.

Lemma unbox_loop_read_refines (known : facts) (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler body : expr) (r : read) (x : variable) (state : loop_state)
    (vars : env) (conts : cont_env) (statics : static_env) (hp : heap) :
  nth_error params (read_position r) = Some x ->
  removes (read_variable r) (read_kind r) (read_primitive r) x handler
    (read_without r) ->
  unbox_loop_read known k params metadata handler body r = Some state ->
  facts_hold known vars statics ->
  refines (State (loop_of k (params, metadata, handler, body)) vars conts
             statics hp)
    (State (loop_of k state) vars conts statics hp).
Proof.
  intros Hx Hremoves Hread Hfacts. unfold unbox_loop_read in Hread.
  rewrite Hx in Hread. simpl in Hread.
  destruct r as [f kind p i without]. simpl in *.
  destruct
    (may_take params metadata f && negb (var_free_b f handler)
     && on_spine f handler)
    eqn:Hchecks; [ | discriminate ].
  apply andb_true_iff in Hchecks as [Hchecks Hspine].
  apply andb_true_iff in Hchecks as [Htake Hfree].
  apply negb_true_iff in Hfree.
  destruct (extend_applications known k i p body) as [body' | ] eqn:Hbody;
    [ | discriminate ].
  simpl in Hread.
  destruct
    (extend_applications
       (facts_under_let (facts_under_params known params) f
          (Prim (Unary p) [Var x]))
       k i p without)
    as [without' | ] eqn:Hwithout; [ | discriminate ].
  simpl in Hread. injection Hread as <-.
  unfold may_take in Htake.
  apply andb_true_iff in Htake as [Htake Hfresh].
  apply andb_true_iff in Htake as [Htake _].
  apply andb_true_iff in Htake as [_ Hdistinct].
  apply negb_true_iff in Hfresh.
  assert (Hne : Pos.eqb x f = false).
  { destruct (Pos.eqb_spec x f) as [Heq | _]; [ | reflexivity ].
    rewrite <- Heq, (nth_error_among x params i Hx) in Hfresh.
    discriminate. }
  set (boxed := Let f kind (Prim (Unary p) [Var x]) without).
  unfold loop_of.
  apply (refines_trans _
    (State (Let_cont_recursive [(k, Handler params metadata boxed)] body)
       vars conts statics hp)).
  - apply (let_cont_recursive_handler_refines_at [] k params metadata handler
      boxed [] body).
    + unfold boxed. simpl. symmetry.
      exact (removes_binds_statics f kind p x handler without Hremoves).
    + intros vs handler_vars conts0 statics0 hp0 _ Hbind.
      destruct (bind_params_value params vs vars handler_vars i x Hbind Hx)
        as [v Hv].
      exact (hoisted_refines f kind p x handler without v handler_vars conts0
        statics0 hp0 Hremoves Hspine Hfree Hne
        (bind_params_nth params vs vars handler_vars i x v Hdistinct Hbind Hx
           Hv)).
  - rewrite <- extend_applications_by_args in Hbody, Hwithout.
    apply (unbox_loop_parameter_refines k i params metadata
      (with_one_more metadata kind) f x kind boxed without'
      (fun known => extend_args known i p) (read_fits i p) Hdistinct Hx
      eq_refl (extend_args_gives i p f x kind without) known body body' vars
      conts statics hp);
      [ | | exact Hbody | exact Hfacts ].
    + intros def_vars bound conts0 statics0 hp0 vs u Hfacts0 Hbind
        (v & Hv & Hgives).
      pose proof (bind_params_nth params vs def_vars bound i x v Hdistinct
        Hbind Hx Hv) as Hlookup.
      destruct (eval_prim statics0 (Unary p) [v]) as [w | ] eqn:Hprim;
        [ | left; exists 1; simpl; unfold boxed; rewrite step_let; simpl;
            rewrite Hlookup; simpl; rewrite Hprim; reflexivity ].
      pose proof (Hgives statics0 (statics_extend_refl statics0) w Hprim)
        as ->.
      destruct (kind_eqb (kind_of_value u) kind) eqn:Hkind;
        [ | left; exists 1; simpl; unfold boxed; rewrite step_let; simpl;
            rewrite Hlookup; simpl; rewrite Hprim, Hkind; reflexivity ].
      right.
      exists without,
        (facts_under_let (facts_under_params known params) f
           (Prim (Unary p) [Var x])).
      split; [ | split; [ exact Hwithout | ] ].
      * unfold boxed. rewrite step_let. simpl. rewrite Hlookup. simpl.
        rewrite Hprim, Hkind. reflexivity.
      * apply facts_hold_under_let;
          [ exact (facts_hold_bind_params statics0 params known vs def_vars
              bound Hfacts0 Hbind)
          | simpl; rewrite Hlookup; simpl; exact Hprim ].
    + unfold boxed. simpl.
      exact (extend_binds_statics k (fun known => extend_args known i p)
        without _ without' Hwithout).
Qed.

(* ======================================================================== *)
(* The pass                                                                 *)
(* ======================================================================== *)

Lemma unbox_loop_param_refines (fuel : nat) :
  ∀ (known : facts) (k : continuation) (i : nat) (state : loop_state)
    (vars : env) (conts : cont_env) (statics : static_env) (hp : heap),
    facts_hold known vars statics ->
    refines (State (loop_of k state) vars conts statics hp)
      (State (loop_of k (unbox_loop_param fuel known k i state)) vars conts
         statics hp).
Proof.
  induction fuel as [ | fuel IH];
    intros known k i state vars conts statics hp Hfacts;
    [ apply refines_refl | ].
  destruct state as [[[params metadata] handler] body]. simpl.
  destruct (nth_error params i) as [param | ] eqn:Hparam; simpl;
    [ | apply refines_refl ].
  destruct (next_read [param] handler) as [r | ] eqn:Hnext; simpl;
    [ | apply refines_refl ].
  destruct
    (unbox_loop_read known k params metadata handler body
       (Read (read_variable r) (read_kind r) (read_primitive r) i
          (read_without r)))
    as [state' | ] eqn:Hread; [ | apply refines_refl ].
  eapply refines_trans; [ | apply IH; exact Hfacts ].
  destruct (next_read_first [param] handler r Hnext) as [wanted Hfirst].
  destruct (first_read_removes handler wanted [param] [] r Hfirst)
    as (x & Hposition & _ & _ & Hremoves).
  apply position_single in Hposition. subst x.
  exact (unbox_loop_read_refines known k params metadata handler body
    (Read (read_variable r) (read_kind r) (read_primitive r) i
       (read_without r))
    param state' vars conts statics hp Hparam Hremoves Hread Hfacts).
Qed.

Lemma unbox_loop_params_refines (fuel : nat) (known : facts)
    (k : continuation) (positions : list nat) :
  ∀ (state : loop_state) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap),
    facts_hold known vars statics ->
    refines (State (loop_of k state) vars conts statics hp)
      (State (loop_of k (unbox_loop_params fuel known k positions state))
         vars conts statics hp).
Proof.
  induction positions as [ | i positions IH];
    intros state vars conts statics hp Hfacts; simpl;
    [ apply refines_refl | ].
  eapply refines_trans; [ | apply IH; exact Hfacts ].
  apply unbox_loop_param_refines, Hfacts.
Qed.

Lemma unbox_loop_reads_refines (known : facts) (k : continuation)
    (params : list variable) (metadata : handler_metadata)
    (handler body : expr) (vars : env) (conts : cont_env)
    (statics : static_env) (hp : heap) :
  facts_hold known vars statics ->
  refines
    (State (Let_cont_recursive [(k, Handler params metadata handler)] body)
       vars conts statics hp)
    (State (unbox_loop_reads known k params metadata handler body) vars conts
       statics hp).
Proof.
  intros Hfacts. unfold unbox_loop_reads.
  exact (unbox_loop_params_refines _ known k _ (params, metadata, handler, body)
    vars conts statics hp Hfacts).
Qed.

Fixpoint unbox_loops_knowing_refines (e : expr) :
  ∀ (known : facts) (vars : env) (conts : cont_env) (statics : static_env)
    (hp : heap),
    facts_hold known vars statics ->
    refines (State e vars conts statics hp)
      (State (unbox_loops_knowing known e) vars conts statics hp).
Proof.
  destruct e
    as [ x kind d body | bindings body | k h body | handlers body | ap
       | ac | scrutinee arms | ];
    intros known vars conts statics hp Hfacts; simpl.
  - apply let_refines_step; [ reflexivity | ].
    intros v Hd _. apply unbox_loops_knowing_refines.
    exact (facts_hold_under_let known x d vars statics v Hfacts Hd).
  - apply let_static_refines_step.
    destruct (eval_static_bindings vars bindings statics) as [extended | ]
      eqn:Hbindings; [ | exact I ].
    apply unbox_loops_knowing_refines.
    exact (facts_hold_under_statics known vars statics bindings extended
      Hfacts Hbindings).
  - destruct h as [params metadata handler].
    apply (refines_trans _
      (State
         (Let_cont_non_recursive k
            (Handler params metadata
               (unbox_loops_knowing (facts_under_params known params)
                  handler))
            body)
         vars conts statics hp)).
    + apply (let_cont_handler_refines_where (facts_hold known vars)
        (facts_hold_extend known vars));
        [ exact Hfacts | ].
      intros vs handler_vars conts0 statics0 hp' Hfacts0 _ Hbind.
      apply unbox_loops_knowing_refines.
      exact (facts_hold_bind_params statics0 params known vs vars
        handler_vars Hfacts0 Hbind).
    + apply let_cont_non_recursive_refines_step.
      apply unbox_loops_knowing_refines, Hfacts.
  - assert (Hbody :
      refines (State (Let_cont_recursive handlers body) vars conts statics hp)
        (State (Let_cont_recursive handlers (unbox_loops_knowing known body))
           vars conts statics hp)).
    { apply let_cont_recursive_refines_step; [ reflexivity | intros _ ].
      apply unbox_loops_knowing_refines, Hfacts. }
    destruct handlers as [ | [k [params metadata handler]] [ | h2 handlers]];
      try exact Hbody.
    eapply refines_trans; [ exact Hbody | ].
    apply unbox_loop_reads_refines, Hfacts.
  - apply refines_refl.
  - apply refines_refl.
  - apply refines_refl.
  - apply refines_refl.
Qed.

Theorem unbox_loops_knowing_symbols_refines :
  unbox_loops_knowing_symbols_refines_statement.
Proof.
  intros known e vars conts statics hp Honly Hbound.
  apply unbox_loops_knowing_refines.
  exact (symbols_facts_hold known vars statics Honly Hbound).
Qed.
