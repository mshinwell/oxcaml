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

(* Proofs of the statements of FlambdaMeetRelationFuelSpec.v. Nothing
   here needs review.

   The meet for an arm is followed down to the one place where a meet
   of less fuel is asked: where the type that a relation gives is
   added to a name. Above that place every function is given two
   meets and is shown to answer the same with both, where the two
   agree on a bare shape and a type with no extension; the
   environment is carried along with what is supposed of it
   ([values_extension_free]), which the demotion of the scrutinee
   keeps, and which each equation that a relation adds keeps: the
   type that a name is given there is a shape, the type that it had,
   or what the meet of the two makes, which has no extension. *)

From Stdlib Require Import ZArith List Bool Lia.
From OxCamlStdlib Require Import OxCamlLogic OxCamlList OxCamlOption.
From OxCamlFlambda2 Require Import FlambdaModel FlambdaMapSpec.
From OxCamlFlambda2Types Require Import FlambdaTypeGrammar FlambdaBindingTime
  FlambdaEnvAliases FlambdaEnvAliasesSpec FlambdaTypingEnv FlambdaMeetGrammar
  FlambdaExpandHead FlambdaMeetEnv FlambdaMeet FlambdaMeetSpec
  FlambdaMeetTerminationSpec FlambdaMeetTerminationProofs FlambdaMeetDepthSpec
  FlambdaMeetDepthProofs FlambdaMeetRelationFuelSpec.
From OxCamlFlambda2 Require FlambdaMapProofs.
From OxCamlFlambda2Types Require FlambdaMeetExamplesSpec
  FlambdaTypeGrammarProofs FlambdaEnvAliasesProofs
  FlambdaTypingEnvInvariantSpec FlambdaTypingEnvInvariantProofs.
Import ListNotations.

(* ======================================================================== *)
(* The types that are added, and the types that they are met with           *)
(* ======================================================================== *)

Theorem choices_get_tag_shapes : choices_get_tag_shapes_statement.
Proof.
  destruct relation_shapes as (_ & _ & _ & _ & Hshapes).
  split; intros tags alloc_mode;
    (split; [ apply (Hshapes tags alloc_mode) | reflexivity ]).
Qed.

(* A type that is an alias has no expansion as one that is not. *)
Lemma alias_not_expanded (ty : flambda_type) :
  get_alias_opt ty <> None -> Expanded_type.of_non_alias_type ty = None.
Proof.
  destruct ty as [ty | ty | k ty | ty | ty];
    destruct ty as [ | [head | s] | ]; cbn; intros Halias;
    first [ reflexivity | contradiction Halias; reflexivity ].
Qed.

(* A type of one of the classes is not an alias, and its expansion is
   of the class and of its kind. *)
Lemma plain_expands (relations : bool) (inside : flambda_type -> bool)
    (ty : flambda_type) :
  plain_type relations inside ty = true ->
  ∃ e : Expanded_type.t,
    Expanded_type.of_non_alias_type ty = Some e
    ∧ plain_type relations inside (Expanded_type.to_type e) = true
    ∧ Expanded_type.kind e = kind ty.
Proof.
  destruct ty as [ty | ty | k ty | ty | ty];
    destruct ty as [ | [head | s] | ]; cbn; try discriminate; intros Hty;
    eexists; (split; [ reflexivity | ]); cbn; (split; [ | reflexivity ]);
    try exact Hty; try reflexivity.
  all: destruct k; reflexivity.
Qed.

(* The expansion of a constant has no extension. *)
Lemma const_extension_free (c : const) :
  extension_free (Expanded_type.to_type (Expanded_type.create_const c))
  = true.
Proof.
  destruct c as [ | | | | | | | | | | | | | | k]; try reflexivity.
  destruct k as [ | [] | | ]; reflexivity.
Qed.

(* ======================================================================== *)
(* Heads of naked immediates                                                *)
(* ======================================================================== *)

(* A case analysis on what a [match] of the goal is on, innermost
   first. *)
Ltac destruct_innermost :=
  match goal with
  | |- context [match ?scrutinee with _ => _ end] =>
    lazymatch scrutinee with
    | context [match _ with _ => _ end] => fail
    | _ => destruct scrutinee eqn:?
    end
  end.

(* The reduction of a head of naked immediates with no relation is
   the head. *)
Lemma reduce_no_relation (tenv : Typing_env.t)
    (head : head_of_kind_naked_immediate) :
  inverse_relations head = [] ->
  reduce_head_of_kind_naked_immediate tenv head = Or_bottom.Ok head.
Proof.
  intros Hnone. unfold reduce_head_of_kind_naked_immediate. rewrite Hnone.
  reflexivity.
Qed.

(* The meet of the numbers of two heads answers the environment that
   it was given. *)
Lemma meet_numbers_env (env env' : Meet_env.t)
    (imms1 imms2 : Or_unknown.t (list Z))
    (r : meet_return_value (Or_unknown.t (list Z))) :
  meet_unknown (fun env s1 s2 => Some (set_meet Z.eqb (fun s => s) env s1 s2))
    Keyed.is_empty env imms1 imms2
  = Some (Meet_result.Ok r env') ->
  env' = env.
Proof.
  unfold meet_unknown, set_meet.
  repeat destruct_innermost; cbn; try discriminate; intros [= _ <-];
    reflexivity.
Qed.

(* ======================================================================== *)
(* The environment once a name is given a type                              *)
(* ======================================================================== *)

(* A name that has no type once another is given one had none
   before. *)
Lemma lookup_before_replace (tenv : Typing_env.t) (n : name)
    (ty : flambda_type) (m : name) :
  Keyed.lookup name_eqb m
    (Typing_env.names_to_types (Typing_env.replace_equation tenv n ty))
  = None ->
  Keyed.lookup name_eqb m (Typing_env.names_to_types tenv) = None.
Proof.
  rewrite FlambdaTypingEnvInvariantProofs.replace_equation_names_to_types.
  assert (Hcons :
    ∀ btm : Binding_time.With_name_mode.t,
      Keyed.lookup name_eqb m
        ((n, (ty, btm)) :: Typing_env.names_to_types tenv)
      = None ->
      Keyed.lookup name_eqb m (Typing_env.names_to_types tenv) = None).
  { intros btm. rewrite FlambdaMapProofs.keyed_lookup_cons.
    destruct
      (FlambdaMapProofs.keyed_eqb_spec name_eqb
         FlambdaTypeGrammarProofs.name_eqb_eq m n);
      [ discriminate | trivial ]. }
  destruct n as [x | sym]; [ | apply Hcons ].
  destruct (Keyed.lookup name_eqb (Name_var x)
              (Typing_env.names_to_types tenv)) as [[ty0 btm0] | ];
    [ apply Hcons | trivial ].
Qed.

(* The type that an environment has for a name once another name is
   given a type: that type, or bottom, or the type it had. *)
Lemma find_after_replace (tenv : Typing_env.t) (n : name) (ty : flambda_type)
    (m : name) (kind : option flambda_kind) (ty1 : flambda_type) :
  Typing_env.find (Typing_env.replace_equation tenv n ty) m kind = Some ty1 ->
  ty1 = ty
  ∨ ty1 = bottom (FlambdaTypeGrammar.kind ty)
  ∨ Typing_env.find tenv m kind = Some ty1.
Proof.
  unfold Typing_env.find, Typing_env.find_with_binding_time_and_mode'.
  assert (Hsymbols :
    Typing_env.defined_symbols (Typing_env.replace_equation tenv n ty)
    = Typing_env.defined_symbols tenv) by reflexivity.
  assert (Hbottom :
    Typing_env.is_bottom (Typing_env.replace_equation tenv n ty)
    = Typing_env.is_bottom tenv) by reflexivity.
  rewrite Hsymbols, Hbottom.
  destruct
    (Keyed.lookup name_eqb m
       (Typing_env.names_to_types (Typing_env.replace_equation tenv n ty)))
    as [[ty0 btm0] | ] eqn:Hlookup.
  - destruct
      (FlambdaTypingEnvInvariantProofs.replace_equation_lookup_cases tenv n ty
         m ty0 btm0 Hlookup) as [[_ ->] | Hbefore].
    + destruct (Typing_env.check_optional_kind_matches ty kind);
        [ | discriminate ].
      destruct (Typing_env.is_bottom tenv); cbn; intros [= <-]; auto.
    + rewrite Hbefore. intros Hfind. right. right. exact Hfind.
  - rewrite (lookup_before_replace tenv n ty m Hlookup).
    intros Hfind. right. right. exact Hfind.
Qed.

Lemma bottom_extension_free (kind : flambda_kind) :
  extension_free (bottom kind) = true.
Proof. destruct kind as [ | [] | | ]; reflexivity. Qed.

(* An environment whose types of kind value have no extension is so
   once a name is given an alias for type, and with other aliases. *)
Lemma replace_by_alias_free (tenv : Typing_env.t) (n : name)
    (ty : flambda_type) :
  get_alias_opt ty <> None ->
  values_extension_free tenv ->
  values_extension_free (Typing_env.replace_equation tenv n ty).
Proof.
  intros Halias Hfree m ty1 Hfind.
  destruct (find_after_replace tenv n ty m _ ty1 Hfind)
    as [-> | [-> | Hbefore]].
  - left. exact Halias.
  - right. apply bottom_extension_free.
  - exact (Hfree m ty1 Hbefore).
Qed.

Lemma with_aliases_free (tenv : Typing_env.t) (aliases : Aliases.t) :
  values_extension_free tenv ->
  values_extension_free (Typing_env.with_aliases tenv aliases).
Proof. intros Hfree m ty Hfind. exact (Hfree m ty Hfind). Qed.

Lemma alias_type_is_alias (kind : flambda_kind) (simple : simple) :
  get_alias_opt (alias_type_of kind simple) <> None.
Proof. destruct kind as [ | [] | | ]; discriminate. Qed.

(* An environment whose types of kind value have no extension is so
   once a name is given a type that has none. *)
Lemma replace_concrete_free (tenv tenv' : Typing_env.t) (n : name)
    (ty : flambda_type) :
  values_extension_free tenv ->
  extension_free ty = true ->
  Meet_env.replace_concrete_equation tenv n ty = Some tenv' ->
  values_extension_free tenv'.
Proof.
  intros Hfree Hty. unfold Meet_env.replace_concrete_equation.
  destruct (must_be_singleton ty) as [[const | ] | ]; [ | | discriminate ].
  - destruct (Aliases.canonical _ _); try discriminate.
    destruct (Typing_env.add_alias tenv (simple_of_name n) (Const const))
      as [[ | result | ] | ] eqn:Hadd; try discriminate.
    destruct (name_eqb _ _ && simple_equal _ _); [ | discriminate ].
    intros [= <-]. apply replace_by_alias_free; [ apply alias_type_is_alias | ].
    unfold Typing_env.add_alias in Hadd.
    destruct (Typing_env.aliases_add tenv _ _) as [[added | ] | ];
      try discriminate Hadd.
    injection Hadd as <-. cbn [Typing_env.add_alias_result_t].
    apply with_aliases_free, Hfree.
  - destruct (get_alias_opt ty); [ discriminate | ]. intros [= <-].
    intros m ty1 Hfind.
    destruct (find_after_replace tenv n ty m _ ty1 Hfind)
      as [-> | [-> | Hbefore]].
    + right. exact Hty.
    + right. apply bottom_extension_free.
    + exact (Hfree m ty1 Hbefore).
Qed.

(* ======================================================================== *)
(* Two meets that agree on a bare shape and a type with no extension        *)
(* ======================================================================== *)

Section Agree.

Variable choices : meet_choices.
Variables mh mh' : meet_expanded_head.
Hypothesis Hshapes : get_tag_shapes choices.
Hypothesis Hagree :
  ∀ (env : Meet_env.t) (e1 e2 : Expanded_type.t),
    bare_shape (Expanded_type.to_type e1) = true ->
    extension_free (Expanded_type.to_type e2) = true ->
    mh env e1 e2 = mh' env e1 e2.
(* On those the second of the two keeps the typing environment, and
   what it makes has no extension. *)
Hypothesis Hkept :
  ∀ (env env' : Meet_env.t) (e1 e2 : Expanded_type.t)
    (r : meet_return_value Expanded_type.t),
    bare_shape (Expanded_type.to_type e1) = true ->
    extension_free (Expanded_type.to_type e2) = true ->
    mh' env e1 e2 = Some (Meet_result.Ok r env') ->
    Meet_env.typing_env env' = Meet_env.typing_env env.
Hypothesis Hmade :
  ∀ (env env' : Meet_env.t) (e1 e2 e : Expanded_type.t),
    bare_shape (Expanded_type.to_type e1) = true ->
    extension_free (Expanded_type.to_type e2) = true ->
    mh' env e1 e2 = Some (Meet_result.Ok (New_result e) env') ->
    extension_free (Expanded_type.to_type e) = true.

Lemma add_shape_on_name (env : Meet_env.t) (x : name) (e : Expanded_type.t) :
  values_extension_free (Meet_env.typing_env env) ->
  bare_shape (Expanded_type.to_type e) = true ->
  Expanded_type.kind e = Value ->
  Meet_env.add_concrete_equation_on_canonical_name true env x e mh
  = Meet_env.add_concrete_equation_on_canonical_name true env x e mh'.
Proof.
  intros Henv Hshape Hkind.
  unfold Meet_env.add_concrete_equation_on_canonical_name. rewrite Hkind.
  destruct (Typing_env.find (Meet_env.typing_env env) x (Some Value))
    as [existing | ] eqn:Hfind; [ | reflexivity ].
  cbn beta iota. destruct (Henv x existing Hfind) as [Halias | Hfree].
  - rewrite (alias_not_expanded existing Halias). reflexivity.
  - destruct (plain_expands true (fun _ => true) existing Hfree)
      as (e_existing & He & Hfree' & _).
    rewrite He. cbn beta iota.
    rewrite (Hagree env e e_existing Hshape Hfree'). reflexivity.
Qed.

Lemma add_shape_on_canonical (env : Meet_env.t) (canonical : simple)
    (e : Expanded_type.t) :
  values_extension_free (Meet_env.typing_env env) ->
  bare_shape (Expanded_type.to_type e) = true ->
  Expanded_type.kind e = Value ->
  Meet_env.add_or_delay_concrete_equation_on_canonical true env canonical e mh
  = Meet_env.add_or_delay_concrete_equation_on_canonical true env canonical e
      mh'.
Proof.
  intros Henv Hshape Hkind.
  unfold Meet_env.add_or_delay_concrete_equation_on_canonical.
  assert (Hname :
    ∀ name : name,
      Meet_env.add_or_delay_concrete_equation_on_canonical_name true env name
        e mh
      = Meet_env.add_or_delay_concrete_equation_on_canonical_name true env
          name e mh').
  { intros name.
    unfold Meet_env.add_or_delay_concrete_equation_on_canonical_name.
    destruct (Keyed.among name_eqb name _); [ reflexivity | ].
    unfold Meet_env.adding_equation_for_name.
    rewrite add_shape_on_name; [ reflexivity | exact Henv | exact Hshape
                               | exact Hkind ]. }
  destruct canonical as [x | sym | c]; [ apply Hname | apply Hname | ].
  unfold Meet_env.add_concrete_equation_on_const.
  rewrite (Hagree env e (Expanded_type.create_const c) Hshape
             (const_extension_free c)).
  reflexivity.
Qed.

Lemma add_shape_equation (env : Meet_env.t) (x : name) (ty : flambda_type) :
  values_extension_free (Meet_env.typing_env env) ->
  bare_shape ty = true ->
  kind ty = Value ->
  Meet_env.add_equation_strict env x ty mh
  = Meet_env.add_equation_strict env x ty mh'.
Proof.
  intros Henv Hshape Hkind.
  unfold Meet_env.add_equation_strict, Meet_env.add_equation0,
    Meet_env.add_equation_on_simple0.
  destruct (Typing_env.is_bottom _); [ reflexivity | ].
  destruct (plain_expands false (fun _ => false) ty Hshape)
    as (e & He & Hshape' & Hkind').
  rewrite (of_non_alias_type_not_alias ty e He), He. cbn beta iota.
  unfold Meet_env.add_concrete_equation_on_simple.
  apply add_shape_on_canonical; [ exact Henv | exact Hshape' | ].
  rewrite Hkind'. exact Hkind.
Qed.

(* The environment once the type of a relation is added to a name has
   what is supposed of it: the type that the name is given is the
   shape, the type it had, or what the meet makes of the two, which
   has no extension. *)
Lemma add_shape_on_name_free (env env' : Meet_env.t) (x : name)
    (e : Expanded_type.t) :
  values_extension_free (Meet_env.typing_env env) ->
  bare_shape (Expanded_type.to_type e) = true ->
  Expanded_type.kind e = Value ->
  Meet_env.add_concrete_equation_on_canonical_name true env x e mh'
  = Some (Or_bottom.Ok env') ->
  values_extension_free (Meet_env.typing_env env').
Proof.
  intros Henv Hshape Hkind.
  unfold Meet_env.add_concrete_equation_on_canonical_name. rewrite Hkind.
  destruct (Typing_env.find (Meet_env.typing_env env) x (Some Value))
    as [existing | ] eqn:Hfind; [ | discriminate ].
  cbn beta iota. destruct (Henv x existing Hfind) as [Halias | Hfree].
  - rewrite (alias_not_expanded existing Halias). discriminate.
  - destruct (plain_expands true (fun _ => true) existing Hfree)
      as (e_existing & He & Hfree' & _).
    rewrite He. cbn beta iota.
    destruct (mh' env e e_existing) as [[r | r env1] | ] eqn:Hmeet;
      cbn beta iota; [ discriminate | | discriminate ].
    pose proof (Hkept env env1 e e_existing r Hshape Hfree' Hmeet) as Henv1.
    assert (Hfree1 : values_extension_free (Meet_env.typing_env env1))
      by (rewrite Henv1; exact Henv).
    destruct r as [ | | | e'].
    + destruct (Meet_env.replace_concrete_equation _ x _) as [tenv | ]
        eqn:Hreplace; [ | discriminate ].
      intros [= <-].
      exact
        (replace_concrete_free _ _ _ _ Hfree1 (plain_type_weaken _ _ _ Hshape)
           Hreplace).
    + intros [= <-]. exact Hfree1.
    + intros [= <-]. exact Hfree1.
    + destruct (Meet_env.replace_concrete_equation _ x _) as [tenv | ]
        eqn:Hreplace; [ | discriminate ].
      intros [= <-].
      exact
        (replace_concrete_free _ _ _ _ Hfree1
           (Hmade env env1 e e_existing e' Hshape Hfree' Hmeet) Hreplace).
Qed.

Lemma add_shape_on_canonical_free (env env' : Meet_env.t) (canonical : simple)
    (e : Expanded_type.t) :
  values_extension_free (Meet_env.typing_env env) ->
  bare_shape (Expanded_type.to_type e) = true ->
  Expanded_type.kind e = Value ->
  Meet_env.add_or_delay_concrete_equation_on_canonical true env canonical e
    mh'
  = Some (Or_bottom.Ok env') ->
  values_extension_free (Meet_env.typing_env env').
Proof.
  intros Henv Hshape Hkind.
  unfold Meet_env.add_or_delay_concrete_equation_on_canonical.
  assert (Hname :
    ∀ name : name,
      Meet_env.add_or_delay_concrete_equation_on_canonical_name true env name
        e mh'
      = Some (Or_bottom.Ok env') ->
      values_extension_free (Meet_env.typing_env env')).
  { intros name.
    unfold Meet_env.add_or_delay_concrete_equation_on_canonical_name.
    destruct (Keyed.among name_eqb name _); [ intros [= <-]; exact Henv | ].
    unfold Meet_env.adding_equation_for_name. cbv zeta.
    match goal with
    | |- match ?added with _ => _ end = _ -> _ =>
      destruct added as [[env1 | ] | ] eqn:Hadded;
        [ | discriminate | discriminate ]
    end.
    intros [= <-]. cbn [Meet_env.typing_env].
    refine (add_shape_on_name_free _ env1 name e _ Hshape Hkind Hadded).
    exact Henv. }
  destruct canonical as [x | sym | c]; [ apply Hname | apply Hname | ].
  unfold Meet_env.add_concrete_equation_on_const.
  destruct (mh' env e (Expanded_type.create_const c)) as [[r | r env1] | ]
    eqn:Hmeet; cbn beta iota; [ discriminate | | discriminate ].
  intros [= <-].
  rewrite (Hkept env env1 e _ r Hshape (const_extension_free c) Hmeet).
  exact Henv.
Qed.

Lemma add_shape_equation_free (env env' : Meet_env.t) (x : name)
    (ty : flambda_type) :
  values_extension_free (Meet_env.typing_env env) ->
  bare_shape ty = true ->
  kind ty = Value ->
  Meet_env.add_equation_strict env x ty mh' = Some (Or_bottom.Ok env') ->
  values_extension_free (Meet_env.typing_env env').
Proof.
  intros Henv Hshape Hkind.
  unfold Meet_env.add_equation_strict, Meet_env.add_equation0,
    Meet_env.add_equation_on_simple0.
  destruct (Typing_env.is_bottom _); [ discriminate | ].
  destruct (plain_expands false (fun _ => false) ty Hshape)
    as (e & He & Hshape' & Hkind').
  rewrite (of_non_alias_type_not_alias ty e He), He. cbn beta iota.
  unfold Meet_env.add_concrete_equation_on_simple.
  apply add_shape_on_canonical_free; [ exact Henv | exact Hshape' | ].
  rewrite Hkind'. exact Hkind.
Qed.

(* One relation, as [reduce_inverse_relations] goes through them: the
   function of its fold, with the meet as a parameter. *)
Definition relation_step (m : meet_expanded_head) (imms : list Z)
    (state : option (Or_bottom.t Meet_env.t)) (inverse : Relation.t * name)
    : option (Or_bottom.t Meet_env.t) :=
  match state with
  | None => None
  | Some Or_bottom.Bottom => Some Or_bottom.Bottom
  | Some (Or_bottom.Ok env) =>
    let name := snd inverse in
    let add_equation (ty : flambda_type) :=
      Meet_env.add_equation_strict env name ty m
    in
    match fst inverse with
    | Relation.Is_null =>
      match Keyed.among Z.eqb 0%Z imms, Keyed.among Z.eqb 1%Z imms with
      | false, false => Some Or_bottom.Bottom
      | true, true => Some (Or_bottom.Ok env)
      | true, false => add_equation any_non_null_value
      | false, true => add_equation null
      end
    | Relation.Is_int =>
      match Keyed.among Z.eqb 0%Z imms, Keyed.among Z.eqb 1%Z imms with
      | false, false => Some Or_bottom.Bottom
      | true, true => Some (Or_bottom.Ok env)
      | true, false => add_equation any_block
      | false, true => add_equation any_tagged_immediate
      end
    | Relation.Get_tag =>
      let tags := Keyed.dedup Z.eqb (filter is_tag imms) in
      match
        type_of_get_tag_scrutinee_or_unknown choices tags
          Alloc_mode.Heap_or_local
      with
      | Or_unknown.Known shape => add_equation shape
      | Or_unknown.Unknown => Some (Or_bottom.Ok env)
      end
    end
  end.

Lemma reduce_inverse_relations_unfold (m : meet_expanded_head)
    (env : Meet_env.t) (imms : list Z) (relations : list (Relation.t * name)) :
  reduce_inverse_relations choices m env (Or_unknown.Known imms) relations
  = List.fold_left (relation_step m imms) relations (Some (Or_bottom.Ok env)).
Proof. reflexivity. Qed.

(* Where the fold is at an environment, that has what is supposed. *)
Definition state_free (state : option (Or_bottom.t Meet_env.t)) : Prop :=
  ∀ env : Meet_env.t,
    state = Some (Or_bottom.Ok env) ->
    values_extension_free (Meet_env.typing_env env).

(* One relation adds one equation at most, of a shape: the two meets
   answer the same, and the environment has what is supposed again. *)
Lemma relation_step_agree (imms : list Z)
    (state : option (Or_bottom.t Meet_env.t)) (inverse : Relation.t * name) :
  state_free state ->
  relation_step mh imms state inverse = relation_step mh' imms state inverse
  ∧ state_free (relation_step mh' imms state inverse).
Proof.
  intros Hstate.
  destruct state as [[env | ] | ]; cbn [relation_step];
    [ | split; [ reflexivity | intros env; discriminate ]
    | split; [ reflexivity | intros env; discriminate ] ].
  pose proof (Hstate env eq_refl) as Henv.
  assert (Hadd :
    ∀ (x : name) (ty : flambda_type),
      bare_shape ty = true ->
      kind ty = Value ->
      Meet_env.add_equation_strict env x ty mh
      = Meet_env.add_equation_strict env x ty mh'
      ∧ state_free (Meet_env.add_equation_strict env x ty mh')).
  { intros x ty Hshape Hkind.
    split; [ exact (add_shape_equation env x ty Henv Hshape Hkind) | ].
    intros env' Hadded.
    exact (add_shape_equation_free env env' x ty Henv Hshape Hkind Hadded). }
  assert (Hsame : state_free (Some (Or_bottom.Ok env)))
    by (intros env' [= <-]; exact Henv).
  assert (Hbottom : state_free (Some Or_bottom.Bottom))
    by (intros env'; discriminate).
  destruct inverse as [relation x]. cbv zeta. cbn [fst snd].
  destruct relation;
    try
      (destruct (Keyed.among Z.eqb 0%Z imms), (Keyed.among Z.eqb 1%Z imms);
       first
         [ split; [ reflexivity | assumption ] | apply Hadd; reflexivity ]).
  unfold type_of_get_tag_scrutinee_or_unknown.
  destruct (forallb is_structured_block _);
    [ | split; [ reflexivity | exact Hsame ] ].
  apply Hadd; apply Hshapes.
Qed.

Lemma relation_fold_agree (imms : list Z)
    (relations : list (Relation.t * name))
    (state : option (Or_bottom.t Meet_env.t)) :
  state_free state ->
  List.fold_left (relation_step mh imms) relations state
  = List.fold_left (relation_step mh' imms) relations state
  ∧ state_free (List.fold_left (relation_step mh' imms) relations state).
Proof.
  revert state.
  induction relations as [ | inverse relations IH]; intros state Hstate;
    cbn [List.fold_left]; [ split; [ reflexivity | exact Hstate ] | ].
  destruct (relation_step_agree imms state inverse Hstate) as [-> Hfree].
  exact (IH _ Hfree).
Qed.

(* The relations of a head of naked immediates say of the names what
   the numbers say: each adds one equation at most, and the type that
   it adds is a shape. *)
Lemma reduce_inverse_relations_agree (env : Meet_env.t)
    (imms : Or_unknown.t (list Z)) (relations : list (Relation.t * name)) :
  values_extension_free (Meet_env.typing_env env) ->
  reduce_inverse_relations choices mh env imms relations
  = reduce_inverse_relations choices mh' env imms relations
  ∧ state_free (reduce_inverse_relations choices mh' env imms relations).
Proof.
  intros Henv.
  destruct imms as [imms | ];
    [ | split; [ reflexivity | intros env' [= <-]; exact Henv ] ].
  rewrite !reduce_inverse_relations_unfold. apply relation_fold_agree.
  intros env' [= <-]. exact Henv.
Qed.

(* The meet of a head of naked immediates with one that has no
   relation. *)
Lemma meet_naked_immediate_agree (env : Meet_env.t)
    (t1 t2 : head_of_kind_naked_immediate) :
  values_extension_free (Meet_env.typing_env env) ->
  inverse_relations t2 = [] ->
  meet_head_of_kind_naked_immediate choices mh env t1 t2
  = meet_head_of_kind_naked_immediate choices mh' env t1 t2.
Proof.
  intros Henv Hnone. unfold meet_head_of_kind_naked_immediate.
  unfold Meet_env.current_typing_env.
  rewrite (reduce_no_relation _ t2 Hnone).
  destruct (reduce_head_of_kind_naked_immediate (Meet_env.typing_env env) t1)
    as [t1' | ]; [ | reflexivity ].
  destruct (meet_unknown _ _ env (naked_immediates t1') (naked_immediates t2))
    as [[r | r env1] | ] eqn:Hnumbers; cbn beta iota; try reflexivity.
  apply meet_numbers_env in Hnumbers. subst env1. cbv zeta.
  destruct (sequence_return_value _) as [head | ]; [ | reflexivity ].
  destruct r as [ | | | imms]; cbn beta iota; try reflexivity;
    rewrite (proj1 (reduce_inverse_relations_agree env _ _ Henv));
    reflexivity.
Qed.

(* A step of the meet, on a head of naked immediates and the head of a
   constant. *)
Lemma step_relation_const_agree (join : join_scoped_envs) (env : Meet_env.t)
    (head : head_of_kind_naked_immediate) (c : const) :
  values_extension_free (Meet_env.typing_env env) ->
  meet_expanded_head_step join choices mh env
    (Expanded_type.create_naked_immediate head) (Expanded_type.create_const c)
  = meet_expanded_head_step join choices mh' env
      (Expanded_type.create_naked_immediate head)
      (Expanded_type.create_const c).
Proof.
  intros Henv. unfold meet_expanded_head_step.
  destruct c;
    cbn [Expanded_type.create_const Expanded_type.create_naked_immediate
         Expanded_type.create_value Expanded_type.create_naked_number
         Expanded_type.create_unknown Expanded_type.descr
         meet_or_unknown_or_bottom meet_expanded_head0];
    try reflexivity.
  match goal with
  | |- context [meet_head_of_kind_naked_immediate choices mh env head ?t2] =>
    rewrite (meet_naked_immediate_agree env head t2 Henv eq_refl)
  end.
  reflexivity.
Qed.

(* The environment that these answer has what is supposed of it. *)
Lemma meet_naked_immediate_free (env env' : Meet_env.t)
    (t1 t2 : head_of_kind_naked_immediate)
    (r : meet_return_value head_of_kind_naked_immediate) :
  values_extension_free (Meet_env.typing_env env) ->
  inverse_relations t2 = [] ->
  meet_head_of_kind_naked_immediate choices mh' env t1 t2
  = Some (Meet_result.Ok r env') ->
  values_extension_free (Meet_env.typing_env env').
Proof.
  intros Henv Hnone. unfold meet_head_of_kind_naked_immediate.
  unfold Meet_env.current_typing_env.
  rewrite (reduce_no_relation _ t2 Hnone).
  destruct (reduce_head_of_kind_naked_immediate (Meet_env.typing_env env) t1)
    as [t1' | ]; [ | discriminate ].
  destruct (meet_unknown _ _ env (naked_immediates t1') (naked_immediates t2))
    as [[r0 | r0 env1] | ] eqn:Hnumbers; cbn beta iota; try discriminate.
  apply meet_numbers_env in Hnumbers. subst env1. cbv zeta.
  destruct (sequence_return_value _) as [head | ]; [ | discriminate ].
  destruct r0 as [ | | | imms]; cbn beta iota;
    first
      [ intros [= _ <-]; exact Henv
      | match goal with
        | |- option_map _
               (reduce_inverse_relations choices mh' env ?numbers ?relations)
             = _ -> _ =>
          pose proof
            (proj2 (reduce_inverse_relations_agree env numbers relations Henv))
            as Hfree;
          destruct (reduce_inverse_relations choices mh' env numbers relations)
            as [[env2 | ] | ] eqn:Hreduce;
          cbn; try discriminate; intros [= _ <-];
          first [ exact (Hfree env2 eq_refl) | exact (Hfree env2 Hreduce) ]
        end ].
Qed.

Lemma step_relation_const_free (join : join_scoped_envs)
    (env env' : Meet_env.t) (head : head_of_kind_naked_immediate) (c : const)
    (r : meet_return_value Expanded_type.t) :
  values_extension_free (Meet_env.typing_env env) ->
  meet_expanded_head_step join choices mh' env
    (Expanded_type.create_naked_immediate head) (Expanded_type.create_const c)
  = Some (Meet_result.Ok r env') ->
  values_extension_free (Meet_env.typing_env env').
Proof.
  intros Henv. unfold meet_expanded_head_step.
  destruct c;
    cbn [Expanded_type.create_const Expanded_type.create_naked_immediate
         Expanded_type.create_value Expanded_type.create_naked_number
         Expanded_type.create_unknown Expanded_type.descr
         meet_or_unknown_or_bottom meet_expanded_head0];
    try discriminate; try (intros [= _ <-]; exact Henv).
  match goal with
  | |- context [meet_head_of_kind_naked_immediate choices mh' env head ?t2] =>
    destruct (meet_head_of_kind_naked_immediate choices mh' env head t2)
      as [[r0 | r0 env1] | ] eqn:Hmeet
  end;
    cbn [option_map]; try discriminate.
  intros Hmap. destruct r0; cbn in Hmap; injection Hmap as _ <-;
    refine (meet_naked_immediate_free env env1 head _ _ Henv _ Hmeet);
    reflexivity.
Qed.

End Agree.

(* ======================================================================== *)
(* The meet of an alias with the type of a constant                         *)
(* ======================================================================== *)

(* The meet of an alias of a canonical name with the type of a
   constant, in an environment whose types of kind value have no
   extension: the one meet that is asked for is that of the type of
   the name with the head of the constant, in an environment that is
   so too. *)
Lemma meet_type_alias_const_free (menv : Meet_env.t) (t ty : flambda_type)
    (n : name) (e : Expanded_type.t) (c : const)
    (mh mh' : meet_expanded_head) :
  aliases_consistent (Typing_env.aliases (Meet_env.typing_env menv)) ->
  is_canonical (Typing_env.aliases (Meet_env.typing_env menv))
    (simple_of_name n) ->
  Typing_env.get_alias_then_canonical_simple_exn (Meet_env.typing_env menv)
    (Some Name_mode.in_types) None t
  = Some (Some (simple_of_name n)) ->
  Typing_env.find (Meet_env.typing_env menv) n (Some (kind t)) = Some ty ->
  Expanded_type.of_non_alias_type ty = Some e ->
  values_extension_free (Meet_env.typing_env menv) ->
  (∀ menv' : Meet_env.t,
    values_extension_free (Meet_env.typing_env menv') ->
    mh menv' e (Expanded_type.create_const c)
    = mh' menv' e (Expanded_type.create_const c)) ->
  Meet_env.meet_type menv t (this_const c) mh
  = Meet_env.meet_type menv t (this_const c) mh'.
Proof.
  intros Hconsistent Hcanonical Hsimple Hfind He Hfree Hagree.
  unfold Meet_env.meet_type, Meet_env.meet.
  destruct (negb (kind_eqb (kind t) (kind (this_const c)))); [ reflexivity | ].
  rewrite Hsimple, canonical_of_const.
  cbn beta iota.
  unfold Meet_env.add_alias_between_canonicals.
  assert (Hne : simple_equal (simple_of_name n) (Const c) = false)
    by (destruct n; reflexivity).
  rewrite Hne.
  unfold Typing_env.add_alias, Typing_env.aliases_add.
  destruct (FlambdaEnvAliasesProofs.add_name_constant _
              (Typing_env.binding_time_resolver (Meet_env.typing_env menv))
              (Typing_env.names_to_types (Meet_env.typing_env menv))
              (Typing_env.aliases (Meet_env.typing_env menv)) n c Hconsistent
              Hcanonical) as [[result [Hadd [Hdemoted Hcanon]]] _].
  rewrite Hadd.
  cbn [Typing_env.add_alias_result_t Typing_env.demoted_name
       Typing_env.canonical_element].
  rewrite Hdemoted, Hcanon.
  unfold Meet_env.record_demotion.
  cbn [Meet_env.typing_env Meet_env.with_typing_env Meet_env.map_typing_env].
  rewrite find_with_aliases, Hfind.
  cbn beta iota.
  unfold expand_head0.
  rewrite (of_non_alias_type_not_alias ty e He), He.
  cbn beta iota delta [Meet_env.add_or_delay_concrete_equation_on_canonical].
  unfold Meet_env.add_concrete_equation_on_const.
  rewrite Hagree; [ reflexivity | ].
  cbn [Meet_env.typing_env Meet_env.with_typing_env Meet_env.map_typing_env].
  apply replace_by_alias_free; [ apply alias_type_is_alias | ].
  apply with_aliases_free, Hfree.
Qed.

(* The same meet answers an environment that has what is supposed,
   where the one meet that is asked for does. *)
Lemma meet_type_alias_const_keeps (menv menv' : Meet_env.t)
    (t ty : flambda_type) (n : name) (e : Expanded_type.t) (c : const)
    (m : meet_expanded_head) (r : meet_return_value flambda_type) :
  aliases_consistent (Typing_env.aliases (Meet_env.typing_env menv)) ->
  is_canonical (Typing_env.aliases (Meet_env.typing_env menv))
    (simple_of_name n) ->
  Typing_env.get_alias_then_canonical_simple_exn (Meet_env.typing_env menv)
    (Some Name_mode.in_types) None t
  = Some (Some (simple_of_name n)) ->
  Typing_env.find (Meet_env.typing_env menv) n (Some (kind t)) = Some ty ->
  Expanded_type.of_non_alias_type ty = Some e ->
  values_extension_free (Meet_env.typing_env menv) ->
  (∀ (menv1 menv2 : Meet_env.t) (r0 : meet_return_value Expanded_type.t),
    values_extension_free (Meet_env.typing_env menv1) ->
    m menv1 e (Expanded_type.create_const c)
    = Some (Meet_result.Ok r0 menv2) ->
    values_extension_free (Meet_env.typing_env menv2)) ->
  Meet_env.meet_type menv t (this_const c) m
  = Some (Meet_result.Ok r menv') ->
  values_extension_free (Meet_env.typing_env menv').
Proof.
  intros Hconsistent Hcanonical Hsimple Hfind He Hfree Hkeeps.
  unfold Meet_env.meet_type, Meet_env.meet.
  destruct (negb (kind_eqb (kind t) (kind (this_const c))));
    [ discriminate | ].
  rewrite Hsimple, canonical_of_const.
  cbn beta iota.
  unfold Meet_env.add_alias_between_canonicals.
  assert (Hne : simple_equal (simple_of_name n) (Const c) = false)
    by (destruct n; reflexivity).
  rewrite Hne.
  unfold Typing_env.add_alias, Typing_env.aliases_add.
  destruct (FlambdaEnvAliasesProofs.add_name_constant _
              (Typing_env.binding_time_resolver (Meet_env.typing_env menv))
              (Typing_env.names_to_types (Meet_env.typing_env menv))
              (Typing_env.aliases (Meet_env.typing_env menv)) n c Hconsistent
              Hcanonical) as [[result [Hadd [Hdemoted Hcanon]]] _].
  rewrite Hadd.
  cbn [Typing_env.add_alias_result_t Typing_env.demoted_name
       Typing_env.canonical_element].
  rewrite Hdemoted, Hcanon.
  unfold Meet_env.record_demotion.
  cbn [Meet_env.typing_env Meet_env.with_typing_env Meet_env.map_typing_env].
  rewrite find_with_aliases, Hfind.
  cbn beta iota.
  unfold expand_head0.
  rewrite (of_non_alias_type_not_alias ty e He), He.
  cbn beta iota delta [Meet_env.add_or_delay_concrete_equation_on_canonical].
  unfold Meet_env.add_concrete_equation_on_const.
  match goal with
  | |- context [m ?demoted e (Expanded_type.create_const c)] =>
    pose proof (Hkeeps demoted) as Hkeeps';
    destruct (m demoted e (Expanded_type.create_const c))
      as [[r0 | r0 menv2] | ] eqn:Hm
  end;
    cbn; try discriminate.
  intros [= _ <-].
  apply (Hkeeps' menv2 r0); [ | first [ exact Hm | reflexivity ] ].
  cbn [Meet_env.typing_env Meet_env.with_typing_env Meet_env.map_typing_env].
  apply replace_by_alias_free; [ apply alias_type_is_alias | ].
  apply with_aliases_free, Hfree.
Qed.

(* ======================================================================== *)
(* The meet for an arm                                                      *)
(* ======================================================================== *)

Theorem relation_const_fuel_enough : relation_const_fuel_enough_statement.
Proof.
  intros join choices tenv t n head c Hjoin Hshapes Hfree Hconsistent
    Hcanonical Hsimple Hfind mh0.
  apply
    (meet_type_alias_const_free (Meet_env.create tenv) t
       (Type_naked_immediate (Ok (No_alias head))) n
       (Expanded_type.create_naked_immediate head) c _ _ Hconsistent
       Hcanonical Hsimple Hfind eq_refl Hfree).
  intros menv' Hfree'.
  change
    (meet_expanded_head_step join choices
       (meet_expanded_head_over join choices mh0 1) menv'
       (Expanded_type.create_naked_immediate head)
       (Expanded_type.create_const c)
     = meet_expanded_head_step join choices
         (Meet.meet_expanded_head join choices 1) menv'
         (Expanded_type.create_naked_immediate head)
         (Expanded_type.create_const c)).
  apply (step_relation_const_agree choices _ _ Hshapes); try assumption.
  - intros env e1 e2 Hshape Hext.
    exact
      (proj1
         (bare_shape_fuel_enough join choices env e1 e2 Hjoin Hshape Hext)
         mh0).
  - intros env env' e1 e2 r Hshape Hext.
    exact
      (proj1
         (bare_shape_meet_adds_nothing join choices env env' e1 e2 r Hjoin
            Hshape Hext)).
  - intros env env' e1 e2 e Hshape Hext.
    exact
      (proj1
         (bare_shape_meet_extension_free join choices env env' e1 e2 e Hjoin
            Hshape Hext)).
Qed.

Theorem relation_const_meet_keeps : relation_const_meet_keeps_statement.
Proof.
  intros join choices fuel tenv tenv' t ty n head c Hjoin Hshapes Hfree
    Hconsistent Hcanonical Hsimple Hfind Hfuel.
  pose proof
    (relation_const_fuel_enough join choices tenv t n head c Hjoin Hshapes
       Hfree Hconsistent Hcanonical Hsimple Hfind) as Henough.
  rewrite
    (proj2
       (meet_fuel_enough_stable join choices 2 fuel tenv t (this_const c)
          Henough Hfuel)).
  unfold Meet.meet.
  destruct (Typing_env.is_bottom tenv); [ discriminate | ].
  destruct
    (Meet_env.meet_type (Meet_env.create tenv) t (this_const c)
       (Meet.meet_expanded_head join choices 2))
    as [[r | r menv'] | ] eqn:Hmeet; try discriminate.
  destruct (is_obviously_bottom _); [ discriminate | ].
  unfold Meet_env.final_typing_env_strict. intros [= _ <-].
  apply
    (meet_type_alias_const_keeps (Meet_env.create tenv) menv' t
       (Type_naked_immediate (Ok (No_alias head))) n
       (Expanded_type.create_naked_immediate head) c
       (Meet.meet_expanded_head join choices 2) r Hconsistent Hcanonical
       Hsimple Hfind eq_refl Hfree);
    [ | exact Hmeet ].
  intros menv1 menv2 r0 Hfree1 Hstep.
  refine
    (step_relation_const_free choices (Meet.meet_expanded_head join choices 1)
       (Meet.meet_expanded_head join choices 1) Hshapes _ _ _ join menv1 menv2
       head c r0 Hfree1 Hstep).
  - intros env e1 e2 _ _. reflexivity.
  - intros env env' e1 e2 r1 Hshape Hext.
    exact
      (proj1
         (bare_shape_meet_adds_nothing join choices env env' e1 e2 r1 Hjoin
            Hshape Hext)).
  - intros env env' e1 e2 e Hshape Hext.
    exact
      (proj1
         (bare_shape_meet_extension_free join choices env env' e1 e2 e Hjoin
            Hshape Hext)).
Qed.

(* ======================================================================== *)
(* An example                                                               *)
(* ======================================================================== *)

(* A test on the types that an environment has: each is not of kind
   value, or is an alias, or has no extension. *)
Definition entry_free (entry : flambda_type * Binding_time.With_name_mode.t)
    : bool :=
  negb (kind_eqb Value (kind (fst entry)))
  || match get_alias_opt (fst entry) with
     | Some _ => true
     | None => extension_free (fst entry)
     end.

Lemma values_extension_free_of_entries (tenv : Typing_env.t) :
  forallb (fun '(_, entry) => entry_free entry)
    (Typing_env.names_to_types tenv)
  = true ->
  values_extension_free tenv.
Proof.
  intros Hall name ty.
  unfold Typing_env.find, Typing_env.find_with_binding_time_and_mode'.
  destruct (Keyed.lookup name_eqb name (Typing_env.names_to_types tenv))
    as [[ty0 btm] | ] eqn:Hlookup.
  - pose proof
      (FlambdaMapProofs.keyed_lookup_forallb name_eqb entry_free name
         (ty0, btm) _ Hall Hlookup) as Hentry.
    unfold Typing_env.check_optional_kind_matches.
    unfold entry_free in Hentry. cbn [fst] in Hentry.
    destruct (kind_eqb Value (kind ty0)); [ | discriminate ].
    cbn [negb orb] in Hentry.
    destruct (Typing_env.is_bottom tenv); cbn; intros [= <-].
    + right. apply bottom_extension_free.
    + destruct (get_alias_opt ty0); [ left; discriminate | right ].
      exact Hentry.
  - destruct name as [x | sym]; [ discriminate | ].
    destruct (among sym (Typing_env.defined_symbols tenv) && _);
      [ | discriminate ].
    cbn. intros [= <-]. right. reflexivity.
Qed.

Theorem example_relation_fuel : example_relation_fuel_statement.
Proof.
  split.
  - intros join choices Hjoin Hshapes.
    assert (Hwf :
      FlambdaTypingEnvInvariantSpec.typing_env_well_formed
        FlambdaMeetExamplesSpec.example_get_tag_env
      = true) by (vm_compute; reflexivity).
    pose proof
      (proj1 (FlambdaTypingEnvInvariantProofs.typing_env_well_formed_iff _)
         Hwf) as Hconditions.
    destruct Hconditions as [_ [_ [Hconsistent _]]].
    apply
      (relation_const_fuel_enough join choices
         FlambdaMeetExamplesSpec.example_get_tag_env
         FlambdaMeetExamplesSpec.example_tag_type
         (Name_var FlambdaMeetExamplesSpec.example_tag)
         (Head_of_kind_naked_immediate Or_unknown.Unknown
            [(Relation.Get_tag, Name_var FlambdaMeetExamplesSpec.example_p)])
         (Naked_immediate 0%Z) Hjoin Hshapes);
      [ apply values_extension_free_of_entries; vm_compute; reflexivity
      | exact Hconsistent
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity ].
  - intros Henough.
    specialize
      (Henough
         (Meet.meet_expanded_head FlambdaMeetExamplesSpec.forgetful_join
            repaired_choices 1)).
    vm_compute in Henough. discriminate Henough.
Qed.

Theorem example_two_relations : example_two_relations_statement.
Proof.
  split; [ | vm_compute; reflexivity ].
  intros join choices Hjoin Hshapes.
  assert (Hwf :
    FlambdaTypingEnvInvariantSpec.typing_env_well_formed
      example_two_relations_env
    = true) by (vm_compute; reflexivity).
  pose proof
    (proj1 (FlambdaTypingEnvInvariantProofs.typing_env_well_formed_iff _)
       Hwf) as Hconditions.
  destruct Hconditions as [_ [_ [Hconsistent _]]].
  apply
    (relation_const_fuel_enough join choices example_two_relations_env
       FlambdaMeetExamplesSpec.example_tag_type
       (Name_var FlambdaMeetExamplesSpec.example_tag)
       (Head_of_kind_naked_immediate Or_unknown.Unknown
          [(Relation.Get_tag, Name_var FlambdaMeetExamplesSpec.example_p);
           (Relation.Is_int, Name_var example_q)])
       (Naked_immediate 1%Z) Hjoin Hshapes);
    [ apply values_extension_free_of_entries; vm_compute; reflexivity
    | exact Hconsistent
    | vm_compute; reflexivity
    | vm_compute; reflexivity
    | vm_compute; reflexivity ].
Qed.
