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


(* Proofs of the statements of FlambdaTupledSpec.v. Nothing here needs
   review. *)

From Stdlib Require Import ZArith List Arith Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlOption OxCamlList.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec
  FlambdaMapProofs FlambdaPrimitiveModel FlambdaValueSpec
  FlambdaPrimitiveSpec FlambdaSemanticsSpec FlambdaSemanticsProofs
  FlambdaPartialApplicationProofs FlambdaWellFormedSpec
  FlambdaWellKindedSpec FlambdaTupledSpec.
Import ListNotations.

(* ======================================================================== *)
(* Tuples                                                                   *)
(* ======================================================================== *)

Lemma skipn_nth_error {A : Type} (l : list A) :
  ∀ (n : nat) (a : A),
    nth_error l n = Some a -> skipn n l = a :: skipn (S n) l.
Proof.
  induction l as [ | b l IH]; intros [ | n] a; simpl; try discriminate.
  - intros [= <-]. reflexivity.
  - intros Hnth. exact (IH n a Hnth).
Qed.

(* The projections of a block of tag 0 with [size] fields of kind
   [Value] read its fields. *)
Lemma tuple_fields_from_block (statics : static_env) (size : nat)
    (tuple : value) (block : list value) :
  block_of statics tuple = Some (0%Z, block) ->
  length block = size ->
  Forall (fun v => kind_of_value v = Value) block ->
  ∀ count field : nat,
    field + count <= size ->
    tuple_fields_from statics size tuple field count
    = Some (firstn count (skipn field block)).
Proof.
  intros Hblock Hlength Hkinds.
  induction count as [ | count IH]; intros field Hle; [ reflexivity | ].
  cbn [tuple_fields_from eval_prim eval_unary_primitive].
  unfold eval_block_load, tuple_access. rewrite Hblock. cbn [known_is].
  rewrite Hlength, !Z.eqb_refl.
  replace (0 <=? Z.of_nat field)%Z with true
    by (symmetry; apply Z.leb_le; lia).
  cbn [andb]. rewrite Nat2Z.id.
  destruct (nth_error block field) as [v | ] eqn:Hnth.
  2: { apply nth_error_None in Hnth. lia. }
  assert (Hv : kind_of_value v = Value).
  { rewrite Forall_forall in Hkinds. apply Hkinds.
    exact (nth_error_In _ _ Hnth). }
  rewrite Hv. cbn [kind_eqb]. rewrite (IH (S field)) by lia.
  rewrite (skipn_nth_error block field v Hnth). reflexivity.
Qed.

Theorem tuple_is_block : tuple_is_block_statement.
Proof.
  intros statics size tuple fields Hsize. split.
  - intros Hfields.
    pose proof (tuple_fields_length _ _ _ _ Hfields) as Hlength.
    pose proof (tuple_fields_kinds _ _ _ _ Hfields) as Hkinds.
    split; [ | split; [ exact Hlength | ] ].
    + destruct (tuple_fields_block _ _ _ _ Hfields) as [-> | Hblock];
        [ simpl in Hlength; destruct (Hsize (eq_sym Hlength)) | exact Hblock ].
    + clear Hfields Hlength. revert size Hsize Hkinds.
      induction fields as [ | v fields IH]; intros size Hsize Hkinds;
        [ apply Forall_nil | ].
      destruct size as [ | size]; [ discriminate | ].
      injection Hkinds as Hv Hrest. apply Forall_cons; [ exact Hv | ].
      destruct fields as [ | w fields]; [ apply Forall_nil | ].
      apply (IH size); [ | exact Hrest ].
      destruct size; [ discriminate | discriminate ].
  - intros (Hblock & Hlength & Hkinds). unfold tuple_fields.
    rewrite (tuple_fields_from_block statics size tuple fields Hblock Hlength
               Hkinds size 0 (Nat.le_refl _)).
    cbn [skipn]. rewrite <- Hlength, firstn_all. reflexivity.
Qed.

(* ======================================================================== *)
(* Calls of tupled code                                                     *)
(* ======================================================================== *)

(* The call of a closure of tupled code whose first argument is a tuple
   is what the call of the code is with the fields of the tuple
   followed by the other arguments. *)
Lemma shape_of_closure_call_tupled (statics : static_env) (callee : value)
    (kind : call_kind) (tuple : value) (rest : list value)
    (first : arity_component) (rest_arity return_arity : arity)
    (called : code_id) (slots : list (value_slot * value)) (c : code)
    (fields : list value) :
  closure_of statics callee = Some (called, slots) ->
  kind = Indirect ∨ kind = Direct called ->
  lookup called (static_code statics) = Some c ->
  code_is_tupled c = true ->
  map kind_of_value (tuple :: rest) = unarize (first :: rest_arity) ->
  unarize_component first = [Value] ->
  tuple_fields statics (cardinal_unarized (code_params_arity c)) tuple
  = Some fields ->
  shape_of_closure_call statics callee kind (tuple :: rest)
    (first :: rest_arity) return_arity
  = shape_of_code_call callee c (fields ++ rest)
      (arity_of_kinds
         (repeat Value (cardinal_unarized (code_params_arity c)))
       ++ rest_arity)
      return_arity.
Proof.
  intros Hclosure Hkind Hcode Htupled Hkinds Hfirst Hfields.
  unfold shape_of_closure_call. rewrite Hclosure.
  assert (Hexpected :
    match kind with
    | Direct named => Pos.eqb called named
    | Indirect => true
    end = true)
    by (destruct Hkind as [-> | ->]; [ reflexivity | apply Pos.eqb_refl ]).
  rewrite Hexpected, Hcode. unfold arguments_for_code, detuple.
  rewrite Htupled, Hkinds, Hfirst, !kinds_eqb_refl. cbn [andb negb].
  rewrite Hfields. reflexivity.
Qed.

(* Code whose parameters are single values has as many of them,
   unarized, as it has variables. *)
Lemma params_are_values_cardinal (c : code) :
  params_are_values c ->
  cardinal_unarized (code_params_arity c) = length (code_params c)
  ∧ length (code_params_arity c) = length (code_params c).
Proof.
  unfold params_are_values, cardinal_unarized. intros ->.
  rewrite unarize_arity_of_kinds. unfold arity_of_kinds.
  rewrite length_map, repeat_length. split; reflexivity.
Qed.

(* A value that has the fields of a tuple of a size that is not zero is
   of kind [Value]. *)
Lemma tuple_kind (statics : static_env) (size : nat) (tuple : value)
    (fields : list value) :
  size <> 0 ->
  tuple_fields statics size tuple = Some fields ->
  kind_of_value tuple = Value.
Proof.
  intros Hsize Hfields.
  destruct (proj1 (tuple_is_block statics size tuple fields Hsize) Hfields)
    as (Hblock & _).
  apply (block_of_kind statics). rewrite Hblock. reflexivity.
Qed.

Lemma params_not_none (c : code) :
  code_params c <> [] -> length (code_params c) <> 0.
Proof. destruct (code_params c); [ congruence | discriminate ]. Qed.

Theorem apply_tupled : apply_tupled_statement.
Proof.
  intros ap vars conts statics callee tuple fields extra called slots c
    Hcallee Hargs Hextra Hclosure Hkind Hcode Htupled Hparams Hsome Harity
    Hfields.
  destruct (params_are_values_cardinal c Hparams) as [Hcardinal Hcount].
  rewrite step_apply, Hcallee, Hargs, Hextra. unfold call_function.
  rewrite (shape_of_call_closure statics callee _ _ _ _
             (closure_not_partial statics callee _ Hclosure)).
  rewrite Harity,
    (shape_of_closure_call_tupled statics callee _ tuple [] _ [] _ called
       slots c fields Hclosure Hkind Hcode Htupled);
    [ | simpl;
        rewrite (tuple_kind statics _ tuple fields (params_not_none c Hsome)
                   Hfields);
        reflexivity
    | reflexivity
    | rewrite Hcardinal; exact Hfields ].
  rewrite !app_nil_r, Hcardinal, <- Hparams. unfold shape_of_code_call.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem apply_tupled_over : apply_tupled_over_statement.
Proof.
  intros ap vars conts statics callee tuple fields rest extra rest_arity
    called slots c Hcallee Hargs Hextra Hclosure Hkind Hcode Htupled Hparams
    Hsome Harity Hnonempty Hkinds Htest Hfields.
  destruct (params_are_values_cardinal c Hparams) as [Hcardinal Hcount].
  pose proof (tuple_kind statics _ tuple fields (params_not_none c Hsome)
                Hfields) as Htuple.
  rewrite step_apply, Hcallee, Hargs, Hextra. unfold call_function.
  rewrite (shape_of_call_closure statics callee _ _ _ _
             (closure_not_partial statics callee _ Hclosure)).
  rewrite Harity,
    (shape_of_closure_call_tupled statics callee _ tuple rest _ rest_arity _
       called slots c fields Hclosure Hkind Hcode Htupled);
    [ | simpl; rewrite Htuple, Hkinds; reflexivity
    | reflexivity
    | rewrite Hcardinal; exact Hfields ].
  rewrite Hcardinal, <- Hparams. unfold shape_of_code_call.
  assert (Hlonger :
    length (code_params_arity c)
    < length (code_params_arity c ++ rest_arity)).
  { rewrite length_app.
    destruct rest_arity; [ destruct (Hnonempty eq_refl) | simpl; lia ]. }
  assert (Hnot_full :
    Nat.eqb (length (code_params_arity c ++ rest_arity))
      (length (code_params_arity c))
    = false)
    by (apply Nat.eqb_neq; lia).
  rewrite Hnot_full.
  assert (Hall :
    map kind_of_value (fields ++ rest)
    = unarize (code_params_arity c ++ rest_arity)).
  { rewrite map_app, (tuple_fields_kinds _ _ _ _ Hfields), Hkinds.
    unfold unarize. rewrite flat_map_app. f_equal.
    change (flat_map unarize_component (code_params_arity c))
      with (unarize (code_params_arity c)).
    unfold params_are_values in Hparams.
    rewrite Hparams, unarize_arity_of_kinds. reflexivity. }
  rewrite Hall, kinds_eqb_refl, Htest. cbn [andb negb].
  apply Nat.ltb_lt in Hlonger. rewrite Hlonger. cbn [run_call].
  unfold partially_apply.
  rewrite Hcardinal, <- (tuple_fields_length _ _ _ _ Hfields),
    firstn_app_exact, skipn_app_exact, firstn_app_exact, skipn_app_exact.
  reflexivity.
Qed.

Theorem apply_tupled_undefined : apply_tupled_undefined_statement.
Proof.
  intros ap vars conts statics callee vs called slots c Hcallee Hargs
    Hclosure Hcode Htupled Hwrong.
  rewrite step_apply, Hcallee, Hargs.
  destruct (eval_simples vars (exn_extra_simples ap)) as [extra | ];
    [ | reflexivity ].
  unfold call_function.
  rewrite (shape_of_call_closure statics callee _ _ _ _
             (closure_not_partial statics callee _ Hclosure)).
  destruct
    (shape_of_closure_call statics callee (ap_call_kind ap) vs
       (ap_args_arity ap) (ap_return_arity ap))
    as [shape | ] eqn:Hshape;
    [ exfalso | reflexivity ].
  apply shape_of_closure_call_cases in Hshape
    as (called' & slots' & c' & vs' & args_arity' & Hclosure' & Hcode' & _
        & Hdetupled & _).
  rewrite Hclosure in Hclosure'. injection Hclosure' as <- <-.
  rewrite Hcode in Hcode'. injection Hcode' as <-.
  unfold arguments_for_code in Hdetupled. rewrite Htupled in Hdetupled.
  apply detuple_cases in Hdetupled
    as (tuple & rest & first & rest_arity & fields & Hvs & Harity & _
        & Hfirst & Hfields & _).
  destruct Hwrong as [-> | [Hno_value | (tuple' & rest' & -> & Hnone)]].
  - discriminate.
  - exact (Hno_value first rest_arity Harity Hfirst).
  - injection Hvs as <- <-. rewrite Hfields in Hnone. discriminate.
Qed.

Theorem tupled_never_partial : tupled_never_partial_statement.
Proof.
  intros statics closure kind vs args_arity return_arity called slots c
    partial Hclosure Hcode Htupled Hshape.
  apply shape_of_closure_call_cases in Hshape
    as (called' & slots' & c' & vs' & args_arity' & Hclosure' & Hcode' & _
        & _ & Hshape).
  rewrite Hclosure in Hclosure'. injection Hclosure' as <- <-.
  rewrite Hcode in Hcode'. injection Hcode' as <-.
  apply shape_of_code_call_cases in Hshape
    as [[_ Hfull] | [(_ & _ & _ & Hover) | (_ & _ & _ & Hnot & _)]].
  - discriminate.
  - discriminate.
  - rewrite Htupled in Hnot. discriminate.
Qed.

(* ======================================================================== *)
(* The examples                                                             *)
(* ======================================================================== *)

Theorem examples_run : examples_run_statement.
Proof.
  intros e [<- | [<- | [<- | []]]]; exists 20; vm_compute; reflexivity.
Qed.

Theorem examples_well_formed : examples_well_formed_statement.
Proof.
  intros e [<- | [<- | [<- | []]]]; split; vm_compute; reflexivity.
Qed.

Theorem wrong_tuple_undefined : wrong_tuple_undefined_statement.
Proof.
  intros e [<- | [<- | []]]; exists 20; vm_compute; reflexivity.
Qed.
