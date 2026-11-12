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

(* Proofs of the statements of FlambdaSimplifyStaticsSpec.v. Nothing
   here needs review. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaKindModel
  FlambdaMapSpec FlambdaMapProofs FlambdaValueSpec FlambdaPrimitiveModel
  FlambdaSemanticsSpec FlambdaSemanticsProofs FlambdaWellFormedSpec
  FlambdaWellFormedProofs FlambdaClosuresProofs FlambdaNominalSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar
  FlambdaTypeGrammarProofs FlambdaTypeMeaningSpec FlambdaTypeMeaningProofs
  FlambdaBindingTime FlambdaTypingEnv FlambdaTypingEnvSpec
  FlambdaTypingEnvProofs FlambdaTypingEnvOperationsSpec
  FlambdaTypingEnvOperationsProofs FlambdaTypingEnvExamplesSpec
  FlambdaTypingEnvRefinementSpec FlambdaTypingEnvRefinementProofs
  FlambdaTypeRenameSpec FlambdaTypeRenameProofs FlambdaEnvRenameSpec
  FlambdaEnvRenameProofs FlambdaProvers FlambdaProversSpec
  FlambdaSimplifyPrimitivesSpec FlambdaSimplifyPrimitivesProofs
  FlambdaSimplifyProjectionsSpec FlambdaSimplifyProjectionsProofs
  FlambdaSimplifyBoxingProofs FlambdaSimplifyStaticsSpec.
Import ListNotations.

Local Open Scope Z_scope.

(* ======================================================================== *)
(* The type of an argument, as a function                                   *)
(* ======================================================================== *)

Theorem argument_type_of : argument_type_of_statement.
Proof.
  intros tenv arg ty. unfold FlambdaSimplifyStaticsSpec.argument_type_of,
    argument_type.
  destruct (Typing_env.mem_simple (Some Name_mode.normal) tenv arg).
  - destruct (Typing_env.type_simple_in_term_exn tenv
                (Some Name_mode.normal) arg)
      as [[[ty' canonical] | ] | ].
    + split.
      * intros [= <-]. split; [ reflexivity | ]. exists canonical.
        reflexivity.
      * intros [_ [canonical' [= <- _]]]. reflexivity.
    + split; [ discriminate | intros [_ [canonical' Heq]]; discriminate ].
    + split; [ discriminate | intros [_ [canonical' Heq]]; discriminate ].
  - split; [ discriminate | intros [Hmem _]; discriminate ].
Qed.

Lemma argument_types_of_typed (tenv : Typing_env.t) (args : list simple) :
  ∀ tys : list flambda_type,
    argument_types_of tenv args = Some tys ->
    Forall2 (argument_type tenv) args tys.
Proof.
  induction args as [ | arg args IH]; intros tys; simpl.
  - intros [= <-]. apply Forall2_nil.
  - destruct (FlambdaSimplifyStaticsSpec.argument_type_of tenv arg)
      as [ty | ] eqn:Hty; [ | discriminate ].
    destruct (argument_types_of tenv args) as [tys' | ]; [ | discriminate ].
    simpl. intros [= <-].
    apply Forall2_cons;
      [ exact (proj1 (argument_type_of tenv arg ty) Hty)
      | exact (IH tys' eq_refl) ].
Qed.

(* ======================================================================== *)
(* A symbol has the type of its constant                                    *)
(* ======================================================================== *)

(* The values of arguments have the types of the arguments. *)
Lemma arguments_typed (tenv : Typing_env.t) (statics : static_env)
    (vars : env) (args : list simple) (tys : list flambda_type) :
  env_satisfies tenv statics vars ->
  Forall2 (argument_type tenv) args tys ->
  ∀ vs : list value,
    eval_simples vars args = Some vs ->
    Forall2 (type_satisfied statics vars) vs tys.
Proof.
  intros Hsat Htys vs Hvs.
  pose proof (eval_simples_values vars args vs Hvs) as Hvalues.
  clear Hvs. revert vs Hvalues.
  induction Htys as [ | arg ty args tys Hty Htys IH]; intros vs Hvalues;
    inversion Hvalues as [ | arg' v args' vs' Hv Hrest]; subst;
    [ apply Forall2_nil | ].
  apply Forall2_cons; [ | exact (IH vs' Hrest) ].
  exact (argument_type_in_machine tenv statics vars arg ty v Hsat Hty Hv).
Qed.

(* Values that have types of the kind value are of the kind value. *)
Lemma kinds_of_values_typed (statics : static_env) (vars : env)
    (vs : list value) (tys : list flambda_type) :
  Forall2 (type_satisfied statics vars) vs tys ->
  forallb (fun ty => kind_eqb (FlambdaTypeGrammar.kind ty) Value) tys = true ->
  map kind_of_value vs = repeat Value (length vs).
Proof.
  intros Htyped. induction Htyped as [ | v ty vs tys Hv Hrest IH]; simpl;
    [ reflexivity | ].
  intros Hkinds. apply andb_true_iff in Hkinds.
  destruct Hkinds as [Hkind Hkinds]. f_equal; [ | exact (IH Hkinds) ].
  rewrite (type_satisfied_kind statics vars v ty Hv).
  destruct (FlambdaTypeGrammar.kind ty); try discriminate. reflexivity.
Qed.

Lemma boxable_number_of_kind_unboxed (kind : flambda_kind)
    (k : boxable_number) :
  boxable_number_of_kind kind = Some k -> kind = unboxed_kind k.
Proof.
  destruct kind as [ | [ | | | | | | | | | | | ] | | ]; simpl;
    try discriminate; intros [= <-]; reflexivity.
Qed.

Theorem static_const_typed : static_const_typed_statement.
Proof.
  intros tenv statics vars s const ty allocated Hsat Htype Heval Hbound.
  unfold static_const_type_in in Htype.
  destruct (argument_types_of tenv (static_const_simples const))
    as [tys | ] eqn:Htys; [ | discriminate Htype ].
  simpl in Htype. apply argument_types_of_typed in Htys.
  destruct const as [code slots | fslot syms decls slots | tag fields
    | contents | bytes];
    simpl in Htype, Htys, Heval; try discriminate Htype.
  - (* A block. *)
    destruct ((tag <? no_scan_tag)
              && forallb
                   (fun ty => kind_eqb (FlambdaTypeGrammar.kind ty) Value)
                   tys) eqn:Hconditions; [ | discriminate Htype ].
    injection Htype as <-. apply andb_true_iff in Hconditions.
    destruct Hconditions as [Htag Hkinds]. apply Z.ltb_lt in Htag.
    destruct (eval_simples vars fields) as [vs | ] eqn:Hvs;
      [ | discriminate Heval ].
    simpl in Heval. injection Heval as <-.
    pose proof (arguments_typed tenv statics vars fields tys Hsat Htys vs Hvs)
      as Htyped.
    apply immutable_block_satisfied. exists vs.
    split; [ unfold block_of; rewrite Hbound; reflexivity | ].
    split; [ | exact Htyped ].
    split; [ exact Htag | ].
    exact (kinds_of_values_typed statics vars vs tys Htyped Hkinds).
  - (* A boxed number. *)
    destruct tys as [ | cty [ | cty' tys]]; try discriminate Htype.
    destruct (boxable_number_of_kind (FlambdaTypeGrammar.kind cty))
      as [k | ] eqn:Hk; [ | discriminate Htype ].
    simpl in Htype. injection Htype as <-.
    inversion Htys as [ | arg ty0 args tys0 Hty _]; subst.
    destruct (eval_simple vars contents) as [v | ] eqn:Hv;
      [ | discriminate Heval ].
    simpl in Heval. injection Heval as <-.
    pose proof (argument_type_in_machine tenv statics vars contents cty v
                  Hsat Hty Hv) as Htyped.
    pose proof (type_satisfied_kind statics vars v cty Htyped) as Hkind.
    rewrite (boxable_number_of_kind_unboxed _ k Hk) in Hkind.
    destruct v as [c | | | | | | | ];
      try (destruct k; discriminate Hkind).
    apply box_number_satisfied. exists c.
    split; [ | split; [ exact Hkind | exact Htyped ] ].
    unfold boxed_number_of. rewrite Hbound.
    unfold boxable_contents, boxable_number_of_const.
    simpl in Hkind. rewrite Hkind.
    destruct k; reflexivity.
  - (* A string. *)
    injection Htype as <-. injection Heval as <-.
    apply this_immutable_string_satisfied. unfold string_of.
    rewrite Hbound. reflexivity.
Qed.

Theorem static_const_type_in_scope : static_const_type_in_scope_statement.
Proof.
  intros tenv const ty y Htype Hy.
  unfold static_const_type_in in Htype.
  destruct (argument_types_of tenv (static_const_simples const))
    as [tys | ] eqn:Htys; [ | discriminate Htype ].
  simpl in Htype. apply argument_types_of_typed in Htys.
  destruct const as [code slots | fslot syms decls slots | tag fields
    | contents | bytes];
    simpl in Htype, Htys; try discriminate Htype.
  - destruct ((tag <? no_scan_tag) && _); [ | discriminate Htype ].
    injection Htype as <-.
    destruct (free_variables_make_block_type tag tys y Hy)
      as [ty [Hin Hfree]].
    clear Hy. induction Htys as [ | arg ty' args tys Hty Htys IH];
      [ contradiction | ].
    destruct Hin as [<- | Hin];
      [ exact (argument_type_in_scope tenv arg ty' y Hty Hfree)
      | exact (IH Hin) ].
  - destruct tys as [ | cty [ | cty' tys]]; try discriminate Htype.
    destruct (boxable_number_of_kind (FlambdaTypeGrammar.kind cty))
      as [k | ]; [ | discriminate Htype ].
    simpl in Htype. injection Htype as <-.
    inversion Htys as [ | arg ty0 args tys0 Hty _]; subst.
    exact (argument_type_in_scope tenv contents cty y Hty
      (box_number_free_variables k cty Alloc_mode.Heap y Hy)).
  - injection Htype as <-. contradiction.
Qed.

(* ======================================================================== *)
(* The environment follows the term                                         *)
(* ======================================================================== *)

Lemma add_symbol_definition_env_satisfies_strictly (tenv : Typing_env.t)
    (s : symbol) (statics : static_env) (vars : env) :
  env_satisfies_strictly tenv statics vars ->
  env_satisfies_strictly (Typing_env.add_symbol_definition tenv s) statics
    vars.
Proof.
  intros [Hbound [valuation [Hsatisfied Hagrees]]].
  split; [ exact Hbound | ]. exists valuation.
  split; [ | exact Hagrees ].
  exact (proj2 (add_symbol_definition_satisfied _ statics valuation tenv s)
    Hsatisfied).
Qed.

Lemma add_symbol_definitions_env_satisfies_strictly (tenv : Typing_env.t)
    (syms : list symbol) (statics : static_env) (vars : env) :
  env_satisfies_strictly tenv statics vars ->
  env_satisfies_strictly (Typing_env.add_symbol_definitions tenv syms)
    statics vars.
Proof.
  intros [Hbound [valuation [Hsatisfied Hagrees]]].
  split; [ exact Hbound | ]. exists valuation.
  split; [ | exact Hagrees ].
  clear Hbound Hagrees. induction syms as [ | sym syms IH].
  - destruct tenv. exact Hsatisfied.
  - exact (proj2 (add_symbol_definition_satisfied _ statics valuation
                    (Typing_env.add_symbol_definitions tenv syms) sym) IH).
Qed.

(* The variables in scope once a symbol is given a type. *)
Lemma replace_symbol_equation_in_scope (tenv : Typing_env.t) (s : symbol)
    (ty : flambda_type) (y : variable) :
  in_scope_in_terms (Typing_env.replace_equation tenv (Name_symbol s) ty) y
  <-> in_scope_in_terms tenv y.
Proof.
  rewrite !in_scope_in_terms_lookup.
  change (Typing_env.min_binding_time
            (Typing_env.replace_equation tenv (Name_symbol s) ty))
    with (Typing_env.min_binding_time tenv).
  rewrite (replace_equation_lookup_other tenv (Name_symbol s) (Name_var y) ty);
    [ reflexivity | discriminate ].
Qed.

(* A symbol is given a type that the pointer which it is has. *)
Lemma replace_symbol_equation_env_satisfies_strictly (tenv : Typing_env.t)
    (statics : static_env) (vars : env) (s : symbol) (ty : flambda_type) :
  (∀ y : variable, y ∈ free_variables ty -> in_scope_in_terms tenv y) ->
  type_satisfied statics vars (Value_symbol s) ty ->
  env_satisfies_strictly tenv statics vars ->
  env_satisfies_strictly (Typing_env.replace_equation tenv (Name_symbol s) ty)
    statics vars.
Proof.
  intros Hfree Htype [Hbound [valuation [Hsatisfied Hagrees]]].
  split.
  - intros y Hy. apply Hbound.
    apply (replace_symbol_equation_in_scope tenv s ty y). exact Hy.
  - exists valuation. split.
    + apply replace_equation_satisfied; [ exact Hsatisfied | ].
      intros v Hv. right. injection Hv as <-.
      apply (type_satisfied_coincide statics vars valuation (Value_symbol s)
               ty);
        [ | exact Htype ].
      intros y Hin. symmetry. exact (Hagrees y (Hfree y Hin)).
    + intros y Hy. apply Hagrees.
      apply (replace_symbol_equation_in_scope tenv s ty y). exact Hy.
Qed.

Theorem symbol_typed_env_satisfies : symbol_typed_env_satisfies_statement.
Proof.
  intros tenv statics vars s const ty allocated Htype Heval Hbound Hsat.
  unfold define_symbol_with_type.
  apply replace_symbol_equation_env_satisfies_strictly.
  - intros y Hy.
    exact (static_const_type_in_scope tenv const ty y Htype Hy).
  - exact (static_const_typed tenv statics vars s const ty allocated
      (env_satisfies_strictly_env_satisfies tenv statics vars Hsat) Htype
      Heval Hbound).
  - apply add_symbol_definition_env_satisfies_strictly. exact Hsat.
Qed.

(* The symbols of a group that are not bound to closures, in a static
   environment that has the whole group bound. *)
Lemma add_block_like_bindings_env_satisfies (statics extended : static_env)
    (vars : env) (all : list static_binding) :
  eval_static_bindings vars all statics = Some extended ->
  ∀ (bindings : list static_binding) (tenv : Typing_env.t),
    (∀ binding : static_binding, binding ∈ bindings -> binding ∈ all) ->
    env_satisfies_strictly tenv extended vars ->
    env_satisfies_strictly (add_block_like_bindings tenv bindings) extended
      vars.
Proof.
  intros Heval.
  induction bindings as [ | [id c | id | s const] bindings IH];
    intros tenv Hall Hsat; simpl.
  - exact Hsat.
  - apply IH; [ intros b Hb; apply Hall; right; exact Hb | exact Hsat ].
  - apply IH; [ intros b Hb; apply Hall; right; exact Hb | exact Hsat ].
  - apply IH; [ intros b Hb; apply Hall; right; exact Hb | ].
    destruct (is_closure_const const); [ exact Hsat | ].
    destruct (static_const_type_in tenv const) as [ty | ] eqn:Htype;
      [ | apply add_symbol_definition_env_satisfies_strictly; exact Hsat ].
    destruct
      (eval_static_bindings_binds vars all statics extended s const Heval
         (Hall _ (or_introl eq_refl)))
      as (allocated & Hconst & Hbound).
    exact (symbol_typed_env_satisfies tenv extended vars s const ty allocated
      Htype Hconst Hbound Hsat).
Qed.

Theorem add_static_bindings_env_satisfies :
  add_static_bindings_env_satisfies_statement.
Proof.
  intros tenv statics extended vars bindings Heval Hsat.
  unfold add_static_bindings.
  apply (add_block_like_bindings_env_satisfies statics extended vars bindings
           Heval);
    [ intros binding Hin; exact Hin | ].
  apply add_symbol_definitions_env_satisfies_strictly.
  exact (env_satisfies_strictly_statics_extend tenv statics extended vars
    (eval_static_bindings_extend vars bindings statics extended Heval) Hsat).
Qed.

Theorem let_static_typed : let_static_typed_statement.
Proof.
  intros tenv bindings body body' Hbody vars conts statics Hsat.
  destruct (eval_static_bindings vars bindings statics) as [extended | ]
    eqn:Hbindings.
  - assert (Hstep :
      ∀ b : expr,
        step (State (Let_static bindings b) vars conts statics)
        = Step (State b vars conts extended)).
    { intros b. rewrite step_let_static, Hbindings. reflexivity. }
    eapply refines_step; [ apply Hstep | apply Hstep | ].
    apply Hbody.
    exact (add_static_bindings_env_satisfies tenv statics extended vars
      bindings Hbindings Hsat).
  - apply step_undefined_refines. rewrite step_let_static, Hbindings.
    reflexivity.
Qed.

(* ======================================================================== *)
(* The symbols defined                                                      *)
(* ======================================================================== *)

Lemma in_closure_symbols_of (bindings : list static_binding) (s : symbol) :
  s ∈ closure_symbols_of bindings
  <-> ∃ const : static_const,
        Bind_symbol s const ∈ bindings ∧ is_closure_const const = true.
Proof.
  induction bindings as [ | [id c | id | s' const] bindings IH]; simpl.
  - split; [ intros [] | intros [const [[] _]] ].
  - rewrite IH. split; intros [const [Hin Hc]]; exists const;
      [ auto | destruct Hin as [[=] | Hin]; auto ].
  - rewrite IH. split; intros [const [Hin Hc]]; exists const;
      [ auto | destruct Hin as [[=] | Hin]; auto ].
  - destruct (is_closure_const const) eqn:Hconst; simpl; rewrite IH.
    + split.
      * intros [<- | [const' [Hin Hc]]];
          [ exists const; auto | exists const'; auto ].
      * intros [const' [[[= <- <-] | Hin] Hc]];
          [ left; reflexivity | right; exists const'; auto ].
    + split.
      * intros [const' [Hin Hc]]. exists const'. auto.
      * intros [const' [[[= <- <-] | Hin] Hc]];
          [ congruence | exists const'; auto ].
Qed.

Lemma defined_symbols_block_like (bindings : list static_binding) :
  ∀ (tenv : Typing_env.t) (s : symbol),
    s ∈ Typing_env.defined_symbols (add_block_like_bindings tenv bindings)
    <-> s ∈ Typing_env.defined_symbols tenv
        ∨ ∃ const : static_const,
            Bind_symbol s const ∈ bindings ∧ is_closure_const const = false.
Proof.
  induction bindings as [ | [id c | id | s' const] bindings IH];
    intros tenv s; simpl.
  - split; [ auto | intros [Hin | [const [[] _]]]; exact Hin ].
  - rewrite IH. split; (intros [Hin | [const [Hin Hc]]]; [ auto | ]);
      right; exists const; [ auto | destruct Hin as [[=] | Hin]; auto ].
  - rewrite IH. split; (intros [Hin | [const [Hin Hc]]]; [ auto | ]);
      right; exists const; [ auto | destruct Hin as [[=] | Hin]; auto ].
  - rewrite IH. destruct (is_closure_const const) eqn:Hconst.
    + split; (intros [Hin | [const' [Hin Hc]]]; [ auto | ]);
        right; exists const'; [ auto | ].
      destruct Hin as [[= <- <-] | Hin]; [ congruence | auto ].
    + assert (Hdefined :
        s ∈ Typing_env.defined_symbols
              match static_const_type_in tenv const with
              | Some ty => define_symbol_with_type tenv s' ty
              | None => Typing_env.add_symbol_definition tenv s'
              end
        <-> s' = s ∨ s ∈ Typing_env.defined_symbols tenv)
        by (destruct (static_const_type_in tenv const); reflexivity).
      rewrite Hdefined. split.
      * intros [[<- | Hin] | [const' [Hin Hc]]];
          [ right; exists const; auto | auto | right; exists const'; auto ].
      * intros [Hin | [const' [[[= <- <-] | Hin] Hc]]];
          [ auto | auto | right; exists const'; auto ].
Qed.

Theorem add_static_bindings_defined_symbols :
  add_static_bindings_defined_symbols_statement.
Proof.
  intros tenv bindings s. unfold add_static_bindings.
  rewrite defined_symbols_block_like.
  change
    (Typing_env.defined_symbols
       (Typing_env.add_symbol_definitions tenv (closure_symbols_of bindings)))
    with (closure_symbols_of bindings ++ Typing_env.defined_symbols tenv).
  rewrite in_app_iff, in_closure_symbols_of. split.
  - intros [[[const [Hin _]] | Hin] | [const [Hin _]]];
      [ right; exists const; exact Hin | left; exact Hin
      | right; exists const; exact Hin ].
  - intros [Hin | [const Hin]]; [ left; right; exact Hin | ].
    destruct (is_closure_const const) eqn:Hconst;
      [ left; left; exists const; auto | right; exists const; auto ].
Qed.

(* ======================================================================== *)
(* Renaming                                                                 *)
(* ======================================================================== *)

Lemma argument_type_of_renamed (r : renaming) (tenv : Typing_env.t)
    (arg : simple) :
  FlambdaSimplifyStaticsSpec.argument_type_of (rename_typing_env r tenv)
    (rename_simple r arg)
  = option_map (rename_type r)
      (FlambdaSimplifyStaticsSpec.argument_type_of tenv arg).
Proof.
  unfold FlambdaSimplifyStaticsSpec.argument_type_of.
  rewrite (mem_simple_equivariant r (Some Name_mode.normal) tenv arg),
    (type_simple_in_term_exn_equivariant r tenv (Some Name_mode.normal) arg).
  destruct (Typing_env.mem_simple (Some Name_mode.normal) tenv arg);
    [ | reflexivity ].
  destruct (Typing_env.type_simple_in_term_exn tenv (Some Name_mode.normal)
              arg) as [[[ty canonical] | ] | ];
    reflexivity.
Qed.

Lemma argument_types_of_renamed (r : renaming) (tenv : Typing_env.t)
    (args : list simple) :
  argument_types_of (rename_typing_env r tenv) (map (rename_simple r) args)
  = option_map (map (rename_type r)) (argument_types_of tenv args).
Proof.
  induction args as [ | arg args IH]; simpl; [ reflexivity | ].
  rewrite argument_type_of_renamed, IH.
  destruct (FlambdaSimplifyStaticsSpec.argument_type_of tenv arg);
    [ | reflexivity ].
  destruct (argument_types_of tenv args); reflexivity.
Qed.

Lemma static_const_simples_renamed (r : renaming) (const : static_const) :
  static_const_simples (rename_static_const r const)
  = map (rename_simple r) (static_const_simples const).
Proof.
  destruct const as [code slots | fslot syms decls slots | tag fields
    | contents | bytes];
    simpl; try reflexivity; rewrite !map_map; reflexivity.
Qed.

Lemma static_const_type_renamed (r : renaming) (const : static_const)
    (tys : list flambda_type) :
  static_const_type (rename_static_const r const) (map (rename_type r) tys)
  = option_map (rename_type r) (static_const_type const tys).
Proof.
  destruct const as [code slots | fslot syms decls slots | tag fields
    | contents | bytes];
    cbn [static_const_type rename_static_const]; try reflexivity.
  - assert (Hkinds :
      forallb (fun ty => kind_eqb (FlambdaTypeGrammar.kind ty) Value)
        (map (rename_type r) tys)
      = forallb (fun ty => kind_eqb (FlambdaTypeGrammar.kind ty) Value) tys).
    { induction tys as [ | ty tys IH]; simpl; [ reflexivity | ].
      rewrite kind_rename_type, IH. reflexivity. }
    rewrite Hkinds.
    destruct ((tag <? no_scan_tag) && _); [ | reflexivity ].
    cbn [option_map]. unfold make_block_type.
    rewrite rename_type_immutable_block. reflexivity.
  - destruct tys as [ | ty [ | ty' tys]]; try reflexivity.
    cbn [map]. rewrite kind_rename_type.
    destruct (boxable_number_of_kind (FlambdaTypeGrammar.kind ty));
      [ | reflexivity ].
    cbn beta iota. cbn [option_map]. rewrite rename_type_box_number.
    reflexivity.
Qed.

Theorem static_const_type_in_rename : static_const_type_in_rename_statement.
Proof.
  intros r tenv const. unfold static_const_type_in.
  rewrite static_const_simples_renamed, argument_types_of_renamed.
  destruct (argument_types_of tenv (static_const_simples const)) as [tys | ];
    [ | reflexivity ].
  simpl. apply static_const_type_renamed.
Qed.

Lemma is_closure_const_renamed (r : renaming) (const : static_const) :
  is_closure_const (rename_static_const r const) = is_closure_const const.
Proof. destruct const; reflexivity. Qed.

Lemma closure_symbols_of_renamed (r : renaming)
    (bindings : list static_binding) :
  closure_symbols_of (map (rename_static_binding r) bindings)
  = closure_symbols_of bindings.
Proof.
  induction bindings as [ | [id c | id | s const] bindings IH]; simpl;
    try exact IH; [ reflexivity | ].
  rewrite is_closure_const_renamed, IH. reflexivity.
Qed.

Lemma add_block_like_bindings_renamed (r : renaming)
    (bindings : list static_binding) :
  ∀ tenv : Typing_env.t,
    add_block_like_bindings (rename_typing_env r tenv)
      (map (rename_static_binding r) bindings)
    = rename_typing_env r (add_block_like_bindings tenv bindings).
Proof.
  induction bindings as [ | [id c | id | s const] bindings IH]; intros tenv;
    simpl; try apply IH; [ reflexivity | ].
  rewrite is_closure_const_renamed.
  destruct (is_closure_const const); [ apply IH | ].
  rewrite (static_const_type_in_rename r tenv const).
  destruct (static_const_type_in tenv const) as [ty | ]; simpl.
  - unfold define_symbol_with_type.
    rewrite (add_symbol_definition_equivariant r tenv s).
    change (Name_symbol s) with (rename_name r (Name_symbol s)) at 1.
    rewrite (replace_equation_equivariant r _ (Name_symbol s) ty).
    apply IH.
  - rewrite (add_symbol_definition_equivariant r tenv s). apply IH.
Qed.

Theorem add_static_bindings_rename : add_static_bindings_rename_statement.
Proof.
  intros r tenv bindings. unfold add_static_bindings.
  rewrite closure_symbols_of_renamed,
    (add_symbol_definitions_equivariant r tenv (closure_symbols_of bindings)).
  apply add_block_like_bindings_renamed.
Qed.

(* ======================================================================== *)
(* An example                                                               *)
(* ======================================================================== *)

Theorem example_load_of_static_block : example_load_of_static_block_statement.
Proof.
  intros k bindings. apply let_static_typed.
  eapply expr_refines_under_trans.
  - (* The load is the [Simple] that the prover answers. *)
    match goal with
    | |- expr_refines_under ?tenv (Let _ _ _ ?body) _ =>
      pose proof (let_block_load tenv example_q Value
                    (Block_access_values (Some 0) (Some 2) Any_value)
                    Immutable 0 (Symbol example_s)
                    (alias_type_of Value (Symbol example_s)) body) as Hload
    end.
    cbv zeta in Hload.
    match type of Hload with
    | context [Provers.meet_block_field_simple ?tenv ?mode ?kind ?ty ?i] =>
      let answer :=
        eval vm_compute in
          (Provers.meet_block_field_simple tenv mode kind ty i)
      in
      replace (Provers.meet_block_field_simple tenv mode kind ty i)
        with answer in Hload by (vm_compute; reflexivity)
    end.
    cbv beta iota in Hload. apply Hload; [ discriminate | ].
    argument_computed.
  - (* The variable of the load is made equal to it. *)
    eapply (let_simple_refines_under _ example_q Value (Var example_x) _ _
              Value);
      [ vm_compute; reflexivity | vm_compute; reflexivity
      | intros ? [= <-]; vm_compute; reflexivity
      | eexists; vm_compute; reflexivity | vm_compute; reflexivity
      | apply expr_equivalent_under_refines; apply apply_cont_canonical;
        apply Forall2_cons; [ canonical_computed | apply Forall2_nil ] ].
Qed.
