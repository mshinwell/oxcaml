(* The natural loops of an SSA graph, from its back edges, and the exit
   branch of a loop's header. The extraction of this file, NaturalLoop.ml,
   is the implementation.

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary, and SsaModel.v for how the models see an SSA graph: blocks
   are abstract, with [predecessors], [all_successors] and [dominates] as
   the compiler provides them. As in the other files, there are four
   parts: (1) the definitions, (2) the intended meaning, (3)
   stepping-stone lemmas, (4) the theorems. Parts 1 and 2 are the part to
   check by eye.

   [natural_loop_body] runs a worklist until the worklist is empty, which
   Rocq cannot see terminates on its own; so its [walk] also stops when a
   list of "fuel" runs out, and [find_loops] passes the graph's block list
   as fuel. That is enough fuel:
   every pop of the worklist corresponds to a block added to the body, and
   a block is added at most once ([natural_loop_body_complete] proves that
   nothing is lost).

   The results, in part 4:

   - [find_loops_back_edges] and [find_loops_complete]: the back edges of
     the loops found are exactly the edges [s -> h] of the graph with [h]
     dominating [s], grouped by [h];
   - [find_loops_body]: a loop's body is its header plus every block from
     which a back-edge source can be reached without passing through the
     header, which is the definition of the natural loop (and in particular
     the body is the same whatever the order of the worklist);
   - [find_exit_branch_spec]: the exit branch found is the header's
     two-way [Switch], one way into the body and the other out of it.

   The trusted part is SsaModel.v: that [predecessors] and
   [all_successors] are the two ends of the same edges, that the block list
   given is the whole graph (which the theorems state as hypotheses), and
   that [dominates] is dominance in the graph (SsaDominance.v says what
   that means). *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlInt OxCamlList.
From OxCamlSsa Require Import SsaModel SsaGraph.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

(* A natural loop: its header, its body, and the sources of its back edges. *)
Record natural_loop : Type :=
  { header : block;
    body : blockset;
    back_edges : list block }.

(* Add a block to the body, and to the worklist [added], when it is not in
   the body yet. *)
Definition add_new (acc : blockset * list block) (p : block)
    : blockset * list block :=
  let '(body, added) := acc in
  if set_mem p body then (body, added) else (set_add p body, p :: added).

(* The worklist walk of [natural_loop_body], with the fuel explained above. *)
Fixpoint walk (fuel : list block) (body : blockset) (worklist : list block)
    : blockset :=
  match fuel, worklist with
  | [], _ | _, [] => body
  | _ :: fuel, bl :: rest =>
    let '(body, added) :=
      OxCamlList.fold_left add_new (body, rest) (predecessors bl)
    in
    walk fuel body added
  end.

(* The body of the loop with header [header] and back-edge sources
   [back_preds]: the header and every block from which a back-edge source
   can be reached without passing through the header. The order of the
   walk does not affect the body it computes. *)
Definition natural_loop_body (fuel : list block) (header : block)
    (back_preds : list block) : blockset :=
  let '(body, seeds) :=
    OxCamlList.fold_left add_new (set_singleton header, []) back_preds
  in
  walk fuel body seeds.

(* Record the back edge [src -> header] in the association list from
   headers to their back-edge sources. *)
Fixpoint add_back_edge (header src : block)
    (tbl : list (block * list block)) : list (block * list block) :=
  match tbl with
  | [] => [(header, [src])]
  | (h, srcs) :: tbl =>
    if block_eqb h header
    then (h, src :: srcs) :: tbl
    else (h, srcs) :: add_back_edge header src tbl
  end.

(* For each block [bl] and each of its successors [succ], record the edge
   if it is a back edge: one whose target dominates its source. *)
Definition record_back_edge (bl : block) (tbl : list (block * list block))
    (succ : block) : list (block * list block) :=
  if dominates succ bl then add_back_edge succ bl tbl else tbl.

Definition record_back_edges (tbl : list (block * list block)) (bl : block)
    : list (block * list block) :=
  OxCamlList.fold_left (record_back_edge bl) tbl (all_successors bl).

(* The natural loops of the graph, given its block list ([Ssa.blocks
   ssa]), in the order their headers are first met. *)
Definition find_loops (blocks : list block) : list natural_loop :=
  let header_tbl := OxCamlList.fold_left record_back_edges [] blocks in
  map
    (fun '(header, back_preds) =>
      {| header := header;
         body := natural_loop_body blocks header back_preds;
         back_edges := back_preds |})
    header_tbl.

(* The header's exit branch: the comparison it tests, which way continues
   the loop, and where the other way goes. *)
Record exit_branch : Type :=
  { condition : value;
    continue_when_true : bool;
    exit_target : block }.

(* The exit branch of a loop: the header's terminator must be a two-target
   [Switch], [ifnot] its false edge and [ifso] its true edge, one of them
   into the body and the other out of it. *)
Definition find_exit_branch (loop : natural_loop) : option exit_branch :=
  match terminator loop.(header) with
  | Terminator.Switch index [ifnot; ifso] =>
    match set_mem ifso loop.(body), set_mem ifnot loop.(body) with
    | true, false =>
      Some {| condition := index;
              continue_when_true := true;
              exit_target := ifnot |}
    | false, true =>
      Some {| condition := index;
              continue_when_true := false;
              exit_target := ifso |}
    | true, true | false, false => None
    end
  | _ => None
  end.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

(* [reaches header sources b]: from [b], one of [sources] can be reached
   along the graph's edges without passing through [header], [b] itself
   not being [header]. The natural loop of the back edges [sources ->
   header] is [header] plus these blocks. *)
Inductive reaches (header : block) (sources : list block) : block -> Prop :=
  | reaches_source : forall s,
      In s sources -> s <> header -> reaches header sources s
  | reaches_pred : forall b p,
      reaches header sources b -> In p (predecessors b) -> p <> header ->
      reaches header sources p.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* --- The walk: soundness --- *)

Section Walk.
  Variable header : block.
  Variable sources : list block.

  (* Every block of the body is the header or reaches a source. *)
  Definition body_sound (body : blockset) : Prop :=
    set_mem header body = true
    /\ forall b, set_mem b body = true ->
         b = header \/ reaches header sources b.

  (* One round of [add_new] over [preds] keeps the body sound and the worklist
     made of blocks that reach a source, when every predecessor added does. *)
  Lemma fold_add_new_sound : forall preds body added,
    body_sound body -> Forall (reaches header sources) added ->
    (forall p, In p preds -> p <> header -> reaches header sources p) ->
    body_sound (fst (List.fold_left add_new preds (body, added)))
    /\ Forall (reaches header sources)
         (snd (List.fold_left add_new preds (body, added))).
  Proof.
    induction preds as [ | p preds IH ]; intros body added Hb Ha Hp.
    - split; assumption.
    - cbn [List.fold_left add_new]. destruct (set_mem p body) eqn:Hm.
      + apply IH; [ assumption | assumption | ].
        intros q Hq. apply Hp. right. exact Hq.
      + assert (Hph : p <> header).
        { intros ->. destruct Hb as [Hh _]. rewrite Hh in Hm. discriminate. }
        assert (Hrp : reaches header sources p)
          by (apply Hp; [ left; reflexivity | exact Hph ]).
        apply IH.
        * destruct Hb as [Hh Hb]. split.
          -- apply set_mem_add_iff. right. exact Hh.
          -- intros b Hin. apply set_mem_add_iff in Hin.
             destruct Hin as [ -> | Hin ];
               [ right; exact Hrp | apply Hb, Hin ].
        * constructor; assumption.
        * intros q Hq. apply Hp. right. exact Hq.
  Qed.

  (* The walk keeps the body sound when the worklist holds only blocks that
     reach a source. *)
  Lemma walk_sound : forall fuel body wl,
    body_sound body -> Forall (reaches header sources) wl ->
    body_sound (walk fuel body wl).
  Proof.
    induction fuel as [ | f fuel IH ]; intros body wl Hb Hw; [ exact Hb | ].
    destruct wl as [ | bl rest ]; [ exact Hb | ].
    cbn [walk]. unfold OxCamlList.fold_left.
    inversion Hw as [ | ? ? Hbl Hrest ]; subst.
    pose proof (fold_add_new_sound (predecessors bl) body rest Hb Hrest
                  (fun p Hp Hne => reaches_pred _ _ _ _ Hbl Hp Hne)) as H.
    destruct (List.fold_left add_new (predecessors bl) (body, rest))
      as [body' wl'].
    cbn [fst snd] in H. destruct H as [H1 H2]. apply IH; assumption.
  Qed.

  (* The body computed is sound, whatever the fuel. *)
  Lemma natural_loop_body_sound_aux : forall fuel,
    body_sound (natural_loop_body fuel header sources).
  Proof.
    intros fuel. unfold natural_loop_body, OxCamlList.fold_left.
    assert (Hb0 : body_sound (set_singleton header)).
    { split; [ apply set_mem_singleton_iff; reflexivity | ].
      intros b Hb. left. apply set_mem_singleton_iff, Hb. }
    pose proof (fold_add_new_sound sources (set_singleton header) [] Hb0
                  (Forall_nil _)
                  (fun s Hs Hne => reaches_source _ _ _ Hs Hne)) as Hf.
    destruct (List.fold_left add_new sources (set_singleton header, []))
      as [body0 seeds].
    cbn [fst snd] in Hf. destruct Hf as [Hf1 Hf2].
    exact (walk_sound fuel body0 seeds Hf1 Hf2).
  Qed.

  (* The header is in the body. *)
  Theorem natural_loop_body_header : forall fuel,
    set_mem header (natural_loop_body fuel header sources) = true.
  Proof. intros fuel. exact (proj1 (natural_loop_body_sound_aux fuel)). Qed.

  (* Every block of the body is the header or reaches a source. *)
  Theorem natural_loop_body_sound : forall fuel b,
    set_mem b (natural_loop_body fuel header sources) = true ->
    b = header \/ reaches header sources b.
  Proof. intros fuel. exact (proj2 (natural_loop_body_sound_aux fuel)). Qed.

  (* --- The walk: completeness --- *)

  Variable blocks : list block.
  Hypothesis blocks_closed : forall b p,
    In b blocks -> In p (predecessors b) -> In p blocks.

  (* The number of blocks of the graph not yet in the body: the measure
     that each pop of the worklist decreases. *)
  Definition absent (body : blockset) : nat :=
    length (filter (fun b => negb (set_mem b body)) blocks).

  (* Every block of the body other than the header, once popped from the
     worklist, has all its predecessors in the body. *)
  Definition closed_except (body : blockset) (wl : list block) : Prop :=
    forall b, set_mem b body = true -> b <> header -> ~ In b wl ->
    forall p, In p (predecessors b) -> set_mem p body = true.

  (* Adding a block of the graph not yet in the body decreases [absent]. *)
  Lemma absent_add : forall body p,
    In p blocks -> set_mem p body = false ->
    absent (set_add p body) < absent body.
  Proof.
    intros body p Hin Hm. unfold absent.
    apply (filter_lt _ _ _ p).
    - intros y Hy. apply negb_true_iff in Hy. apply negb_true_iff.
      destruct (set_mem y body) eqn:E; [ | reflexivity ].
      rewrite <- Hy. symmetry. apply set_mem_add_iff. right. exact E.
    - exact Hin.
    - rewrite Hm. reflexivity.
    - apply negb_false_iff. apply set_mem_add_iff. left. reflexivity.
  Qed.

  (* [absent] is at most the number of blocks. *)
  Lemma absent_le_length : forall body, absent body <= length blocks.
  Proof. intros body. apply length_filter_le. Qed.

  (* What one round of additions does. *)
  Lemma fold_add_new_spec : forall preds body added body' added',
    List.fold_left add_new preds (body, added) = (body', added') ->
    (forall p, In p preds -> In p blocks) ->
    (forall b, set_mem b body = true -> set_mem b body' = true)
    /\ (forall p, In p preds -> set_mem p body' = true)
    /\ (forall b, set_mem b body' = true ->
          set_mem b body = true \/ In b added')
    /\ (forall b, In b added -> In b added')
    /\ ((forall b, In b added -> set_mem b body = true) ->
        forall b, In b added' -> set_mem b body' = true)
    /\ length added' + absent body' <= length added + absent body
    /\ (forall b, In b added' -> In b added \/ In b preds).
  Proof.
    induction preds as [ | p preds IH ]; intros body added body' added' H Hin.
    - cbn [List.fold_left] in H. injection H as <- <-.
      repeat split; try tauto; [ intros b [] | lia ].
    - cbn [List.fold_left add_new] in H. destruct (set_mem p body) eqn:Hm.
      + specialize (IH _ _ _ _ H (fun q Hq => Hin q (or_intror Hq))).
        destruct IH as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
        repeat split; try assumption.
        * intros q [ -> | Hq ]; [ apply H1, Hm | apply H2, Hq ].
        * intros b Hb. destruct (H7 b Hb) as [Hb' | Hb'].
          -- left. exact Hb'.
          -- right. right. exact Hb'.
      + specialize (IH _ _ _ _ H (fun q Hq => Hin q (or_intror Hq))).
        destruct IH as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
        assert (Hpb : In p blocks) by (apply Hin; left; reflexivity).
        pose proof (absent_add body p Hpb Hm) as Habs.
        repeat split.
        * intros b Hb. apply H1. apply set_mem_add_iff. right. exact Hb.
        * intros q [ -> | Hq ].
          -- apply H1. apply set_mem_add_iff. left. reflexivity.
          -- apply H2, Hq.
        * intros b Hb. destruct (H3 b Hb) as [Hb' | Hb'].
          -- apply set_mem_add_iff in Hb'. destruct Hb' as [ -> | Hb' ].
             ++ right. apply H4. left. reflexivity.
             ++ left. exact Hb'.
          -- right. exact Hb'.
        * intros b Hb. apply H4. right. exact Hb.
        * intros Hadd b Hb. apply H5; [ | exact Hb ].
          intros q [ -> | Hq ].
          -- apply set_mem_add_iff. left. reflexivity.
          -- apply set_mem_add_iff. right. apply Hadd, Hq.
        * cbn [length] in H6. lia.
        * intros b Hb. destruct (H7 b Hb) as [ [ -> | Hb' ] | Hb' ].
          -- right. left. reflexivity.
          -- left. exact Hb'.
          -- right. right. exact Hb'.
  Qed.

  (* With enough fuel ([length wl + absent body]), the walk keeps every block
     of the body and ends with a body closed under predecessors, except at the
     header. *)
  Lemma walk_complete : forall fuel body wl,
    (forall b, In b wl -> set_mem b body = true) ->
    (forall b, set_mem b body = true -> In b blocks) ->
    closed_except body wl ->
    length wl + absent body <= length fuel ->
    (forall b, set_mem b body = true -> set_mem b (walk fuel body wl) = true)
    /\ closed_except (walk fuel body wl) [].
  Proof.
    induction fuel as [ | f fuel IH ]; intros body wl Hwl Hbl Hcl Hn.
    - destruct wl as [ | bl rest ].
      + cbn [walk]. split; [ tauto | exact Hcl ].
      + cbn [length] in Hn. lia.
    - destruct wl as [ | bl rest ].
      + cbn [walk]. split; [ tauto | exact Hcl ].
      + cbn [walk]. unfold OxCamlList.fold_left.
        destruct (List.fold_left add_new (predecessors bl) (body, rest))
          as [body1 added1] eqn:Hf.
        assert (Hpreds : forall p, In p (predecessors bl) -> In p blocks).
        { intros p Hp. apply (blocks_closed bl); [ | exact Hp ].
          apply Hbl, Hwl. left. reflexivity. }
        destruct (fold_add_new_spec _ _ _ _ _ Hf Hpreds)
          as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
        assert (Hwl1 : forall b, In b added1 -> set_mem b body1 = true).
        { apply H5. intros b Hb. apply Hwl. right. exact Hb. }
        assert (Hbl1 : forall b, set_mem b body1 = true -> In b blocks).
        { intros b Hb. destruct (H3 b Hb) as [Hb' | Hb'].
          - apply Hbl, Hb'.
          - destruct (H7 b Hb') as [Hr | Hp].
            + apply Hbl, Hwl. right. exact Hr.
            + apply Hpreds, Hp. }
        assert (Hcl1 : closed_except body1 added1).
        { intros b Hb Hbh Hnin p Hp.
          destruct (H3 b Hb) as [Hb' | Hb']; [ | contradiction ].
          destruct (block_eqb b bl) eqn:E.
          - apply block_eqb_spec in E. subst b. apply H2, Hp.
          - apply H1. apply (Hcl b Hb' Hbh); [ | exact Hp ].
            intros [ -> | Hr ].
            + rewrite block_eqb_refl in E. discriminate.
            + apply Hnin, H4, Hr. }
        assert (Hn1 : length added1 + absent body1 <= length fuel).
        { cbn [length] in Hn. lia. }
        destruct (IH body1 added1 Hwl1 Hbl1 Hcl1 Hn1) as [IH1 IH2].
        split; [ | exact IH2 ].
        intros b Hb. apply IH1, H1, Hb.
  Qed.

  (* With the graph's blocks as fuel, the body holds every source and is closed
     under predecessors, except at the header. *)
  Lemma natural_loop_body_complete_aux :
    In header blocks -> (forall s, In s sources -> In s blocks) ->
    (forall s, In s sources ->
       set_mem s (natural_loop_body blocks header sources) = true)
    /\ closed_except (natural_loop_body blocks header sources) [].
  Proof.
    intros Hh Hs. unfold natural_loop_body, OxCamlList.fold_left.
    destruct (List.fold_left add_new sources (set_singleton header, []))
      as [body0 seeds] eqn:Hf.
    destruct (fold_add_new_spec _ _ _ _ _ Hf Hs)
      as [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]].
    assert (Hwl : forall b, In b seeds -> set_mem b body0 = true).
    { apply H5. intros b []. }
    assert (Hbl : forall b, set_mem b body0 = true -> In b blocks).
    { intros b Hb. destruct (H3 b Hb) as [Hb' | Hb'].
      - apply set_mem_singleton_iff in Hb'. subst b. exact Hh.
      - destruct (H7 b Hb') as [ [] | Hb'' ]. apply Hs, Hb''. }
    assert (Hcl : closed_except body0 seeds).
    { intros b Hb Hbh Hnin p Hp. exfalso.
      destruct (H3 b Hb) as [Hb' | Hb'].
      - apply set_mem_singleton_iff in Hb'. exact (Hbh Hb').
      - exact (Hnin Hb'). }
    assert (Hn : length seeds + absent body0 <= length blocks).
    { cbn [length] in H6.
      pose proof (absent_le_length (set_singleton header)). lia. }
    destruct (walk_complete blocks body0 seeds Hwl Hbl Hcl Hn) as [W1 W2].
    split; [ | exact W2 ].
    intros s Hs'. apply W1, H2, Hs'.
  Qed.

  (* A block that reaches a source is not the header. *)
  Lemma reaches_not_header : forall b,
    reaches header sources b -> b <> header.
  Proof. intros b H. destruct H; assumption. Qed.

  (* Every block that reaches a source without passing through the header is in
     the body. *)
  Theorem natural_loop_body_complete : forall b,
    In header blocks -> (forall s, In s sources -> In s blocks) ->
    reaches header sources b ->
    set_mem b (natural_loop_body blocks header sources) = true.
  Proof.
    intros b Hh Hs Hr.
    destruct (natural_loop_body_complete_aux Hh Hs) as [Hsrc Hcl].
    induction Hr as [ s Hin Hne | b p Hr IH Hp Hne ].
    - apply Hsrc, Hin.
    - apply (Hcl b IH (reaches_not_header b Hr)); [ intros [] | exact Hp ].
  Qed.
End Walk.

(* --- [find_loops] --- *)

Section FindLoops.
  Variable blocks : list block.
  Hypothesis blocks_closed : forall b p,
    In b blocks -> In p (predecessors b) -> In p blocks.
  Hypothesis succs_closed : forall b s,
    In b blocks -> In s (all_successors b) -> In s blocks.

  (* The invariant of the table: every entry records back edges. *)
  Definition tbl_sound (tbl : list (block * list block)) : Prop :=
    forall h srcs, In (h, srcs) tbl ->
      srcs <> []
      /\ forall s, In s srcs ->
           In s blocks /\ In h (all_successors s) /\ dominates h s = true.

  Definition tbl_has (tbl : list (block * list block)) (h s : block) : Prop :=
    exists srcs, In (h, srcs) tbl /\ In s srcs.

  (* The entries after [add_back_edge h s]: a new entry [(h, [s])], the entry
     of [h] with [s] added, or an entry left alone. *)
  Lemma add_back_edge_entries : forall h s tbl h' srcs',
    In (h', srcs') (add_back_edge h s tbl) ->
    (h' = h /\ srcs' = [s])
    \/ (h' = h /\ exists srcs, In (h, srcs) tbl /\ srcs' = s :: srcs)
    \/ In (h', srcs') tbl.
  Proof.
    intros h s tbl. induction tbl as [ | [h0 srcs0] tbl IH ];
      intros h' srcs' Hin.
    - destruct Hin as [E | [] ]. injection E as <- <-. left. auto.
    - cbn in Hin. destruct (block_eqb h0 h) eqn:E.
      + apply block_eqb_spec in E. subst h0. destruct Hin as [E' | Hin].
        * injection E' as <- <-. right. left. split; [ reflexivity | ].
          exists srcs0. split; [ left; reflexivity | reflexivity ].
        * right. right. right. exact Hin.
      + destruct Hin as [E' | Hin].
        * injection E' as <- <-. right. right. left. reflexivity.
        * destruct (IH h' srcs' Hin) as [H | [ [Hh [srcs [H1 H2]]] | H ] ].
          -- left. exact H.
          -- right. left. split; [ exact Hh | ].
             exists srcs. split; [ right; exact H1 | exact H2 ].
          -- right. right. right. exact H.
  Qed.

  (* After [add_back_edge h s] the table has [s] as a source of [h] ... *)
  Lemma add_back_edge_has_new : forall h s tbl,
    tbl_has (add_back_edge h s tbl) h s.
  Proof.
    intros h s tbl. induction tbl as [ | [h0 srcs0] tbl IH ].
    - exists [s]. split; left; reflexivity.
    - cbn. destruct (block_eqb h0 h) eqn:E.
      + apply block_eqb_spec in E. subst h0.
        exists (s :: srcs0). split; left; reflexivity.
      + destruct IH as [srcs [H1 H2]].
        exists srcs. split; [ right; exact H1 | exact H2 ].
  Qed.

  (* ... and keeps every source it had. *)
  Lemma add_back_edge_has_old : forall h s tbl h' s',
    tbl_has tbl h' s' -> tbl_has (add_back_edge h s tbl) h' s'.
  Proof.
    intros h s tbl. induction tbl as [ | [h0 srcs0] tbl IH ];
      intros h' s' [srcs [Hin Hs]].
    - destruct Hin.
    - cbn. destruct (block_eqb h0 h) eqn:E.
      + destruct Hin as [E' | Hin].
        * injection E' as -> ->. exists (s :: srcs).
          split; [ left; reflexivity | right; exact Hs ].
        * exists srcs. split; [ right; exact Hin | exact Hs ].
      + destruct Hin as [E' | Hin].
        * injection E' as -> ->. exists srcs.
          split; [ left; reflexivity | exact Hs ].
        * destruct (IH h' s' (ex_intro _ srcs (conj Hin Hs)))
            as [srcs' [H1 H2]].
          exists srcs'. split; [ right; exact H1 | exact H2 ].
  Qed.

  (* [record_back_edge], unfolded. *)
  Lemma record_back_edge_eq : forall bl tbl h,
    record_back_edge bl tbl h
    = if dominates h bl then add_back_edge h bl tbl else tbl.
  Proof. reflexivity. Qed.

  (* Recording the back edges among the successors [succs] of [bl]: the table
     stays sound, keeps what it had, and gains each successor that dominates
     [bl]. *)
  Lemma fold_succs_spec : forall bl succs tbl,
    In bl blocks -> (forall s, In s succs -> In s (all_successors bl)) ->
    tbl_sound tbl ->
    let tbl' := List.fold_left (record_back_edge bl) succs tbl in
    tbl_sound tbl'
    /\ (forall h s, tbl_has tbl h s -> tbl_has tbl' h s)
    /\ (forall h, In h succs -> dominates h bl = true -> tbl_has tbl' h bl).
  Proof.
    intros bl succs. induction succs as [ | h succs IH ];
      intros tbl Hbl Hsucc Hs; cbv zeta.
    - cbn [List.fold_left]. split; [ exact Hs | split; [ tauto | ] ].
      intros h [].
    - cbn [List.fold_left]. rewrite record_back_edge_eq.
      assert (Hsucc' : forall s, In s succs -> In s (all_successors bl))
        by (intros s Hs'; apply Hsucc; right; exact Hs').
      destruct (dominates h bl) eqn:Hd.
      + assert (Hs1 : tbl_sound (add_back_edge h bl tbl)).
        { intros h' srcs' Hin.
          destruct (add_back_edge_entries _ _ _ _ _ Hin)
            as [ [-> ->] | [ [-> [srcs [Hin' ->]]] | Hin' ] ].
          - split; [ discriminate | ].
            intros s [ -> | [] ].
            split; [ exact Hbl | split; [ | exact Hd ] ].
            apply Hsucc. left. reflexivity.
          - destruct (Hs h srcs Hin') as [_ Hall].
            split; [ discriminate | ].
            intros s [ -> | Hs' ].
            + split; [ exact Hbl | split; [ | exact Hd ] ].
              apply Hsucc. left. reflexivity.
            + apply Hall, Hs'.
          - apply Hs, Hin'. }
        destruct (IH _ Hbl Hsucc' Hs1) as [S1 [S2 S3]].
        split; [ exact S1 | split ].
        * intros h' s H. apply S2, add_back_edge_has_old, H.
        * intros h' [ -> | Hh ] Hd'.
          -- apply S2, add_back_edge_has_new.
          -- apply S3; assumption.
      + destruct (IH _ Hbl Hsucc' Hs) as [S1 [S2 S3]].
        split; [ exact S1 | split; [ exact S2 | ] ].
        intros h' [ -> | Hh ] Hd'.
        * rewrite Hd in Hd'. discriminate.
        * apply S3; assumption.
  Qed.

  (* The same over a list of blocks: the table gains every back edge among
     their successors. *)
  Lemma fold_blocks_spec : forall bls tbl,
    (forall b, In b bls -> In b blocks) -> tbl_sound tbl ->
    let tbl' := List.fold_left record_back_edges bls tbl in
    tbl_sound tbl'
    /\ (forall h s, tbl_has tbl h s -> tbl_has tbl' h s)
    /\ (forall h s, In s bls -> In h (all_successors s) ->
          dominates h s = true -> tbl_has tbl' h s).
  Proof.
    induction bls as [ | bl bls IH ]; intros tbl Hin Hs; cbv zeta.
    - cbn [List.fold_left]. split; [ exact Hs | split; [ tauto | ] ].
      intros h s [].
    - cbn [List.fold_left].
      change (record_back_edges tbl bl)
        with (List.fold_left (record_back_edge bl) (all_successors bl) tbl).
      destruct (fold_succs_spec bl (all_successors bl) tbl
                  (Hin bl (or_introl eq_refl)) (fun s Hs' => Hs') Hs)
        as [S1 [S2 S3]].
      destruct (IH _ (fun b Hb => Hin b (or_intror Hb)) S1) as [T1 [T2 T3]].
      split; [ exact T1 | split ].
      + intros h s H. apply T2, S2, H.
      + intros h s [ -> | Hbs ] Hh Hd.
        * apply T2. apply S3; assumption.
        * apply T3; assumption.
  Qed.

  (* The table [find_loops] builds is sound and holds every back edge of the
     graph. *)
  Lemma header_tbl_spec :
    let tbl := List.fold_left record_back_edges blocks [] in
    tbl_sound tbl
    /\ (forall h s, In s blocks -> In h (all_successors s) ->
          dominates h s = true -> tbl_has tbl h s).
  Proof.
    cbv zeta.
    destruct (fold_blocks_spec blocks [] (fun b Hb => Hb)
                ltac:(intros h srcs [])) as [S1 [_ S3]].
    split; assumption.
  Qed.

  (* The loops found are exactly the entries of the table, each with its body
     computed. *)
  Lemma find_loops_In : forall l,
    In l (find_loops blocks) <->
    exists h srcs,
      In (h, srcs) (List.fold_left record_back_edges blocks [])
      /\ l = {| header := h;
                body := natural_loop_body blocks h srcs;
                back_edges := srcs |}.
  Proof.
    intros l. unfold find_loops, OxCamlList.fold_left. cbv zeta.
    rewrite in_map_iff. split.
    - intros [ [h srcs] [<- Hin] ]. exists h, srcs. split; [ exact Hin | ].
      reflexivity.
    - intros [h [srcs [Hin ->]]]. exists (h, srcs). split; [ reflexivity | ].
      exact Hin.
  Qed.

  (* Every back edge of a loop found is an edge of the graph whose target, the
     header, dominates its source. *)
  Theorem find_loops_back_edges : forall l s,
    In l (find_loops blocks) -> In s l.(back_edges) ->
    In s blocks /\ In l.(header) (all_successors s)
    /\ dominates l.(header) s = true.
  Proof.
    intros l s Hl Hs. apply find_loops_In in Hl.
    destruct Hl as [h [srcs [Hin ->]]]. cbn [header back_edges] in *.
    destruct header_tbl_spec as [S1 _].
    exact (proj2 (S1 h srcs Hin) s Hs).
  Qed.

  (* Every edge whose target dominates its source is a back edge of a loop
     found, with that target as header. *)
  Theorem find_loops_complete : forall s h,
    In s blocks -> In h (all_successors s) -> dominates h s = true ->
    exists l,
      In l (find_loops blocks) /\ l.(header) = h /\ In s l.(back_edges).
  Proof.
    intros s h Hs Hh Hd.
    destruct header_tbl_spec as [_ S3].
    destruct (S3 h s Hs Hh Hd) as [srcs [Hin Hsrc]].
    exists {| header := h;
              body := natural_loop_body blocks h srcs;
              back_edges := srcs |}.
    split; [ | split; [ reflexivity | exact Hsrc ] ].
    apply find_loops_In. exists h, srcs. split; [ exact Hin | reflexivity ].
  Qed.

  (* The body of a loop found is its header plus the blocks that reach a
     back-edge source without passing through the header. *)
  Theorem find_loops_body : forall l b,
    In l (find_loops blocks) ->
    (set_mem b l.(body) = true
     <-> b = l.(header) \/ reaches l.(header) l.(back_edges) b).
  Proof.
    intros l b Hl. apply find_loops_In in Hl.
    destruct Hl as [h [srcs [Hin ->]]]. cbn [header body back_edges].
    destruct header_tbl_spec as [S1 _].
    destruct (S1 h srcs Hin) as [Hne Hall].
    split.
    - apply natural_loop_body_sound.
    - intros [ -> | Hr ].
      + apply natural_loop_body_header.
      + apply (natural_loop_body_complete h srcs blocks blocks_closed);
          [ | | exact Hr ].
        * destruct srcs as [ | s srcs' ]; [ contradiction | ].
          destruct (Hall s (or_introl eq_refl)) as [Hsb [Hhs _]].
          exact (succs_closed s h Hsb Hhs).
        * intros s Hs. exact (proj1 (Hall s Hs)).
  Qed.
End FindLoops.

(* --- [find_exit_branch] --- *)

(* The exit branch found is the header's two-way [Switch] on [condition];
   the loop continues along the edge [continue_when_true] names, which is
   into the body, and the other edge leaves it. *)
Theorem find_exit_branch_spec : forall l eb,
  find_exit_branch l = Some eb ->
  exists ifnot ifso,
    terminator l.(header) = Terminator.Switch eb.(condition) [ifnot; ifso]
    /\ set_mem ifso l.(body) = eb.(continue_when_true)
    /\ set_mem ifnot l.(body) = negb eb.(continue_when_true).
Proof.
  intros l eb H. unfold find_exit_branch in H.
  destruct (terminator l.(header)) as [ | index targets | | ] eqn:Ht;
    try discriminate.
  destruct targets as [ | ifnot [ | ifso [ | ] ] ]; try discriminate.
  exists ifnot, ifso.
  destruct (set_mem ifso l.(body)) eqn:Hso;
    destruct (set_mem ifnot l.(body)) eqn:Hnot; try discriminate;
    injection H as <-; cbn; repeat split.
Qed.
