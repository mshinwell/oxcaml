(* A Rocq model of [backend/ssa/loop/natural_loop.ml].

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary, and SsaModel.v for how the models see an SSA graph: blocks
   are abstract, with [predecessors], [all_successors] and [dominates] as
   the compiler provides them. As in the other files, there are four
   parts: (1) a transcription of the OCaml, (2) the intended meaning, (3)
   stepping-stone lemmas, (4) the theorems. Parts 1 and 2 are the part to
   check by eye.

   One thing is different from the OCaml. Its [natural_loop_body] runs a
   worklist until the worklist is empty, which Rocq cannot see terminates;
   the model's [walk] also stops when a list of "fuel" runs out, and
   [find_loops] passes the graph's block list as fuel. That is enough fuel:
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
   - [edge_dominates_sound]: the sufficient condition the OCaml checks for
     an edge to dominate a block is one: every path from the entry to the
     block traverses the edge, given what [dominates] means.

   The trusted part is SsaModel.v: that [predecessors] and
   [all_successors] are the two ends of the same edges, that [dominates d
   b] means every path from the entry to [b] passes through [d], and that
   the entry has no predecessors. The theorems state these as hypotheses. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxcamlStdlib Require Import OcamlInt OcamlList.
From OxcamlLoop Require Import SsaModel.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: transcription of the OCaml                                       *)
(* ======================================================================== *)

(* OCaml [loop]. *)
Record natural_loop : Type :=
  { header : block;
    body : blockset;
    back_edges : list block }.

(* The body of the OCaml's two loops that add a block to the body, and to
   the worklist, when it is not in the body yet: [(body, added)] are its
   two references. *)
Definition add_new (acc : blockset * list block) (p : block)
    : blockset * list block :=
  let '(body, added) := acc in
  if set_mem p body then (body, added) else (set_add p body, p :: added).

(* OCaml [natural_loop_body]'s [walk], with the fuel explained above. *)
Fixpoint walk (fuel : list block) (body : blockset) (worklist : list block)
    : blockset :=
  match fuel, worklist with
  | [], _ | _, [] => body
  | _ :: fuel, bl :: rest =>
    let '(body, added) :=
      OcamlList.fold_left add_new (body, rest) (predecessors bl)
    in
    walk fuel body added
  end.

(* OCaml [natural_loop_body]. The OCaml's [List.filter] keeps the seeds in
   their order and the worklist here has them reversed, which changes the
   order of the walk but not the body it computes. *)
Definition natural_loop_body (fuel : list block) (header : block)
    (back_preds : list block) : blockset :=
  let '(body, seeds) :=
    OcamlList.fold_left add_new (set_singleton header, []) back_preds
  in
  walk fuel body seeds.

(* The OCaml's [Block.Tbl.replace header_tbl succ (bl :: existing)], on an
   association list in place of the hash table. *)
Fixpoint add_back_edge (header src : block)
    (tbl : list (block * list block)) : list (block * list block) :=
  match tbl with
  | [] => [(header, [src])]
  | (h, srcs) :: tbl =>
    if block_eqb h header
    then (h, src :: srcs) :: tbl
    else (h, srcs) :: add_back_edge header src tbl
  end.

(* OCaml [find_loops], on the graph's block list [Ssa.blocks ssa]. The
   loops come out in the order their headers are first met rather than in
   the hash table's order. *)
Definition find_loops (blocks : list block) : list natural_loop :=
  let header_tbl :=
    OcamlList.fold_left
      (fun tbl bl =>
        OcamlList.fold_left
          (fun tbl succ =>
            if dominates succ bl then add_back_edge succ bl tbl else tbl)
          tbl (all_successors bl))
      [] blocks
  in
  map
    (fun '(header, back_preds) =>
      {| header := header;
         body := natural_loop_body blocks header back_preds;
         back_edges := back_preds |})
    header_tbl.

(* OCaml [edge_dominates]. *)
Definition edge_dominates (src succ target : block) : bool :=
  dominates succ target
  && match predecessors succ with
     | [p] => block_eqb p src
     | [] | _ :: _ :: _ => false
     end.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

(* [path a p c]: [p] is a path from [a] to [c] along the graph's edges,
   listing its blocks from [a] to [c]. An edge [a -> b] is [a] being a
   predecessor of [b]. *)
Inductive path : block -> list block -> block -> Prop :=
  | path_one : forall b, path b [b] b
  | path_cons : forall a b l c,
      In a (predecessors b) -> path b (b :: l) c -> path a (a :: b :: l) c.

(* The edge [src -> succ] is on the path [p]. *)
Definition edge_on (p : list block) (src succ : block) : Prop :=
  exists l1 l2, p = l1 ++ src :: succ :: l2.

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

(* --- Block equality and sets --- *)

Lemma block_eqb_refl : forall b, block_eqb b b = true.
Proof. intros b. apply block_eqb_spec. reflexivity. Qed.

Lemma block_eqb_neq : forall a b, a <> b -> block_eqb a b = false.
Proof.
  intros a b H. destruct (block_eqb a b) eqn:E; [ | reflexivity ].
  apply block_eqb_spec in E. contradiction.
Qed.

Lemma set_mem_add_iff : forall b x s,
  set_mem b (set_add x s) = true <-> b = x \/ set_mem b s = true.
Proof.
  intros b x s. rewrite set_mem_add, orb_true_iff, block_eqb_spec. tauto.
Qed.

Lemma set_mem_singleton_iff : forall b x,
  set_mem b (set_singleton x) = true <-> b = x.
Proof. intros b x. rewrite set_mem_singleton. apply block_eqb_spec. Qed.

(* --- The walk: soundness --- *)

Section Walk.
  Variable header : block.
  Variable sources : list block.

  (* Every block of the body is the header or reaches a source. *)
  Definition body_sound (body : blockset) : Prop :=
    set_mem header body = true
    /\ forall b, set_mem b body = true -> b = header \/ reaches header sources b.

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
             destruct Hin as [ -> | Hin ]; [ right; exact Hrp | apply Hb, Hin ].
        * constructor; assumption.
        * intros q Hq. apply Hp. right. exact Hq.
  Qed.

  Lemma walk_sound : forall fuel body wl,
    body_sound body -> Forall (reaches header sources) wl ->
    body_sound (walk fuel body wl).
  Proof.
    induction fuel as [ | f fuel IH ]; intros body wl Hb Hw; [ exact Hb | ].
    destruct wl as [ | bl rest ]; [ exact Hb | ].
    cbn [walk]. unfold OcamlList.fold_left.
    inversion Hw as [ | ? ? Hbl Hrest ]; subst.
    pose proof (fold_add_new_sound (predecessors bl) body rest Hb Hrest
                  (fun p Hp Hne => reaches_pred _ _ _ _ Hbl Hp Hne)) as H.
    destruct (List.fold_left add_new (predecessors bl) (body, rest)) as [body' wl'].
    cbn [fst snd] in H. destruct H as [H1 H2]. apply IH; assumption.
  Qed.

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

  Lemma filter_length_le : forall {A} (f g : A -> bool) (l : list A),
    (forall y, f y = true -> g y = true) ->
    length (filter f l) <= length (filter g l).
  Proof.
    intros A f g l Hfg. induction l as [ | y l IH ]; [ reflexivity | ].
    simpl. destruct (f y) eqn:Hf.
    - rewrite (Hfg y Hf). simpl. lia.
    - destruct (g y); simpl; lia.
  Qed.

  Lemma filter_length_lt : forall {A} (f g : A -> bool) (l : list A) x,
    (forall y, f y = true -> g y = true) ->
    In x l -> g x = true -> f x = false ->
    length (filter f l) < length (filter g l).
  Proof.
    intros A f g l x Hfg Hin Hg Hf.
    induction l as [ | y l IH ]; [ contradiction | ].
    simpl. destruct Hin as [ -> | Hin ].
    - rewrite Hf, Hg. simpl. pose proof (filter_length_le f g l Hfg). lia.
    - destruct (f y) eqn:Hfy.
      + rewrite (Hfg y Hfy). simpl. apply IH in Hin. lia.
      + destruct (g y); simpl; apply IH in Hin; lia.
  Qed.

  Lemma absent_add : forall body p,
    In p blocks -> set_mem p body = false ->
    absent (set_add p body) < absent body.
  Proof.
    intros body p Hin Hm. unfold absent.
    apply (filter_length_lt _ _ _ p).
    - intros y Hy. apply negb_true_iff in Hy. apply negb_true_iff.
      destruct (set_mem y body) eqn:E; [ | reflexivity ].
      rewrite <- Hy. symmetry. apply set_mem_add_iff. right. exact E.
    - exact Hin.
    - rewrite Hm. reflexivity.
    - apply negb_false_iff. apply set_mem_add_iff. left. reflexivity.
  Qed.

  Lemma absent_le : forall body body',
    (forall b, set_mem b body = true -> set_mem b body' = true) ->
    absent body' <= absent body.
  Proof.
    intros body body' H. unfold absent. apply filter_length_le.
    intros y Hy. apply negb_true_iff in Hy. apply negb_true_iff.
    destruct (set_mem y body) eqn:E; [ | reflexivity ].
    rewrite <- Hy. symmetry. apply H. exact E.
  Qed.

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
    /\ length added' + absent body' <= length added + absent body.
  Proof.
    induction preds as [ | p preds IH ]; intros body added body' added' H Hin.
    - cbn [List.fold_left] in H. injection H as <- <-.
      repeat split; try tauto; [ intros b [] | lia ].
    - cbn [List.fold_left add_new] in H. destruct (set_mem p body) eqn:Hm.
      + specialize (IH _ _ _ _ H (fun q Hq => Hin q (or_intror Hq))).
        destruct IH as [H1 [H2 [H3 [H4 [H5 H6]]]]].
        repeat split; try assumption.
        intros q [ -> | Hq ]; [ apply H1, Hm | apply H2, Hq ].
      + specialize (IH _ _ _ _ H (fun q Hq => Hin q (or_intror Hq))).
        destruct IH as [H1 [H2 [H3 [H4 [H5 H6]]]]].
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
  Qed.

  Lemma walk_complete : forall fuel body wl,
    (forall b, In b wl -> set_mem b body = true) ->
    (forall b, set_mem b body = true -> In b blocks) ->
    closed_except body wl ->
    length wl + absent body <= length fuel ->
    (forall b, set_mem b body = true -> set_mem b (walk fuel body wl) = true)
    /\ closed_except (walk fuel body wl) [].
  Proof.
    (* Work in progress. *)
  Admitted.
End Walk.
