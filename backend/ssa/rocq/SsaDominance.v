(* Dominance in an SSA graph, beyond the [dominates] test SsaModel.v takes
   from the compiler: strict dominance, the test that a block is entered
   from one block only, and what dominance means in terms of paths. The
   extraction of this file, SsaDominance.ml, is the implementation.

   See the reading guide at the top of backend/ssa/loop/rocq/
   LoopComparisons.v for the Rocq vocabulary and SsaModel.v for how the
   models see an SSA graph. As there, the file has four parts: (1) the
   definitions, (2) the intended meaning, (3) stepping-stone lemmas, (4)
   the theorems. Parts 1 and 2 are the part to check by eye.

   The result, in part 4, is [edge_on_every_path]: when [succ] dominates
   [target] and is entered only from [pred], every path from the entry to
   [target] takes the edge [pred -> succ]. This is how AffineSsa.v knows
   which way the branch of a dominator went.

   The trusted part is SsaModel.v: that [predecessors] lists the sources of
   the edges into a block, that [dominates d b] means every path from the
   entry to [b] passes through [d], and that the entry dominates every block
   (every block of a finished graph is reachable from it). The last two
   are [dominance_semantics] in part 2, which the theorem assumes. *)

From Stdlib Require Import Bool List Lia PeanoNat.
From OxCamlSsa Require Import SsaModel SsaGraph.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

(* [dominator] dominates [block] and is not it. *)
Definition strictly_dominates (dominator block : block) : bool :=
  dominates dominator block && negb (block_eqb dominator block).

(* [pred] is the sole predecessor of [succ], which is not the graph's
   entry: control enters [succ] only from [pred]. The entry has a
   predecessor when the function calls itself in tail position ([Continue
   (Goto entry)]), yet is also entered from outside; on a finished graph,
   where every block is reachable from the entry, a block that dominates
   its only predecessor can only be the entry, which the first test
   excludes. *)
Definition sole_predecessor (pred succ : block) : bool :=
  negb (dominates succ pred)
  && match predecessors succ with
     | [only_pred] => block_eqb only_pred pred
     | [] | _ :: _ :: _ => false
     end.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

(* [path first p last]: [p] is a path from [first] to [last] along the
   graph's edges, listing its blocks from [first] to [last]. An edge
   [pred -> succ] is [pred] being a predecessor of [succ]. *)
Inductive path : block -> list block -> block -> Prop :=
  | path_one : forall (block : block), path block [block] block
  | path_cons : forall (pred succ : block) (rest : list block) (last : block),
      In pred (predecessors succ) -> path succ (succ :: rest) last ->
      path pred (pred :: succ :: rest) last.

(* The edge [pred -> succ] is on the path [p]. *)
Definition edge_on (p : list block) (pred succ : block) : Prop :=
  exists before after, p = before ++ pred :: succ :: after.

(* What the compiler's [dominates], written [--dom-->], means, [entry]
   being the graph's entry block: every path from the entry to [target]
   passes through each dominator of [target], and the entry dominates every
   block, each being reachable from it. Nothing is assumed of the entry's
   predecessors: a self-recursive tail call is a back edge to the entry. *)
Record dominance_semantics (entry : block) : Prop :=
  { dominates_spec : forall (dominator target : block),
      dominator --dom--> target ->
      forall (p : list block), path entry p target -> In dominator p;
    entry_dominates : forall (block : block), entry --dom--> block }.

Arguments dominates_spec {entry}.
Arguments entry_dominates {entry}.

(* A program point is a block and the number of instructions still to
   execute. The entry point has the full body remaining; point zero is
   the terminator. Result definitions become available after their
   instruction, while parameters are available at the block entry. *)
Definition point : Type := block * nat.

Definition entry_point (b : block) : point := (b, length (block_body b)).

Definition point_eqb (lhs rhs : point) : bool :=
  block_eqb (fst lhs) (fst rhs) && Nat.eqb (snd lhs) (snd rhs).

(* Instruction edges advance through a block. Terminator edges use the
   same successor observation as block dominance, including exceptional
   successors even though the restricted semantics cannot take them. *)
Inductive point_edge : point -> point -> Prop :=
  | Point_instruction : forall (b : block) (insns_left : nat),
      insns_left < length (block_body b) ->
      point_edge (b, S insns_left) (b, insns_left)
  | Point_transfer : forall (source target : block),
      In target (all_successors source) ->
      point_edge (source, 0) (entry_point target).

Inductive point_path : point -> list point -> point -> Prop :=
  | Point_path_one : forall (p : point), point_path p [p] p
  | Point_path_cons : forall (first next last : point) (rest : list point),
      point_edge first next -> point_path next (next :: rest) last ->
      point_path first (first :: next :: rest) last.

Definition point_dominates (entry : block) (dominator target : point)
    : Prop :=
  forall (points : list point),
    point_path (entry_point entry) points target -> In dominator points.

Definition point_reachable (entry : block) (target : point) : Prop :=
  exists (points : list point), point_path (entry_point entry) points target.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* Point equality compares the block identity and instruction position. *)
Lemma point_eqb_spec : forall (lhs rhs : point),
  point_eqb lhs rhs = true <-> lhs = rhs.
Proof.
  intros [b n] [b' n']. unfold point_eqb; cbn.
  rewrite andb_true_iff, block_eqb_spec, Nat.eqb_eq.
  split; [intros [-> ->]; reflexivity | intros H; inversion H; auto].
Qed.

(* Every path contains its endpoint, so each point dominates itself. *)
Lemma point_dominates_refl : forall (entry : block) (position : point),
  point_dominates entry position position.
Proof.
  intros entry position points Hpath. induction Hpath;
    [left; reflexivity | right; exact IHHpath].
Qed.

(* A point path can be extended at either end by one graph edge. *)
Lemma point_path_prepend : forall (first next last : point)
    (points : list point),
  point_edge first next -> point_path next points last ->
  point_path first (first :: points) last.
Proof.
  intros first next last points Hedge Hpath.
  inversion Hpath; subst; apply Point_path_cons; assumption.
Qed.

Lemma point_path_snoc : forall (first last next : point)
    (points : list point),
  point_path first points last -> point_edge last next ->
  point_path first (points ++ [next]) next.
Proof.
  intros first last next points Hpath. induction Hpath; intros Hedge; cbn.
  - apply Point_path_cons; [exact Hedge | constructor].
  - apply Point_path_cons; [assumption | apply IHHpath; exact Hedge].
Qed.

(* Join two paths without requiring a self-edge at their shared point. *)
Lemma point_path_join : forall (first middle last : point)
    (prefix suffix : list point),
  point_path first prefix middle -> point_path middle suffix last ->
  exists (joined : list point), point_path first joined last /\
    forall (member : point), In member joined ->
      In member prefix \/ In member suffix.
Proof.
  intros first middle last prefix suffix Hprefix Hsuffix.
  induction Hprefix.
  - exists suffix. split; [exact Hsuffix | auto].
  - destruct (IHHprefix Hsuffix) as [joined [Hjoined Hmembers]].
    exists (first :: joined). split.
    + eapply point_path_prepend; eassumption.
    + intros member [<- | Hin]; [left; left; reflexivity |].
      destruct (Hmembers member Hin); [left; right | right]; assumption.
Qed.

(* Keep the suffix starting at the last occurrence of a selected point. *)
Lemma point_path_last_visit : forall (first last : point)
    (points : list point),
  point_path first points last -> forall (selected : point),
  In selected points -> exists (tail : list point),
    point_path selected (selected :: tail) last /\ ~ In selected tail.
Proof.
  intros first last points Hpath. induction Hpath;
    intros selected Hin.
  - destruct Hin as [<- | []]. exists []. split; [constructor | tauto].
  - destruct (existsb (point_eqb selected) (next :: rest)) eqn:Hlater.
    + apply existsb_exists in Hlater. destruct Hlater as [p [Hp Heq]].
      apply point_eqb_spec in Heq. subst p. apply IHHpath. exact Hp.
    + destruct Hin as [<- | Hin].
      * exists (next :: rest). split; [econstructor; eassumption |].
        intros Hin. assert (existsb (point_eqb first) (next :: rest) = true).
        { apply existsb_exists. exists first. split; [exact Hin |].
          apply point_eqb_spec. reflexivity. }
        congruence.
      * assert (existsb (point_eqb selected) (next :: rest) = true).
        { apply existsb_exists. exists selected. split; [exact Hin |].
          apply point_eqb_spec. reflexivity. }
        congruence.
Qed.

(* A path avoiding a region's entry point after its start cannot leave
   and re-enter a region closed under all other incoming edges. *)
Lemma point_path_region_suffix : forall (inside : point -> Prop)
    (cut : point),
  (forall (before after : point), point_edge before after ->
     inside after -> after <> cut -> inside before) ->
  forall (first last : point) (points : list point),
  point_path first points last -> inside last ->
  ~ In cut (tl points) -> Forall inside points.
Proof.
  intros inside cut Hclosed first last points Hpath.
  induction Hpath; intros Hlast Havoid.
  - constructor; [exact Hlast | constructor].
  - assert (Htail : Forall inside (next :: rest)).
    { apply IHHpath; [exact Hlast |]. cbn in *. tauto. }
    constructor; [ | exact Htail].
    eapply Hclosed; [exact H | inversion Htail; assumption |].
    intros Heq. subst next. apply Havoid. left. reflexivity.
Qed.

(* Truncate a path at its first visit to the destination. *)
Lemma point_path_first_visit : forall (first last : point)
    (points : list point),
  point_path first points last ->
  exists (prefix : list point),
    point_path first (prefix ++ [last]) last /\ ~ In last prefix.
Proof.
  intros first last points Hpath. induction Hpath.
  - exists []. split; [constructor | cbn; tauto].
  - destruct (point_eqb first last) eqn:E.
    + apply point_eqb_spec in E. subst first.
      exists []. split; [constructor | cbn; tauto].
    + destruct IHHpath as [prefix [Hp Hnot]].
      exists (first :: prefix). split.
      * cbn. eapply point_path_prepend; eassumption.
      * intros [Heq | Hin]; [ | contradiction].
        subst first. assert (point_eqb last last = true)
          by (apply point_eqb_spec; reflexivity). congruence.
Qed.

(* A member of an avoiding prefix can be reached without leaving that
   prefix. This is the path-splicing fact needed for antisymmetry. *)
Lemma point_path_prefix_avoiding : forall (first last : point)
    (points : list point),
  point_path first points last ->
  forall (prefix suffix : list point) (member avoid : point),
  points = prefix ++ suffix -> ~ In avoid prefix -> In member prefix ->
  exists (before_member : list point),
    point_path first before_member member /\ ~ In avoid before_member.
Proof.
  intros first last points Hpath. induction Hpath;
    intros prefix suffix member avoid Heq Havoid Hin;
    destruct prefix as [ | head prefix]; [contradiction | | contradiction |].
  - cbn in Heq. injection Heq as <- Htail.
    destruct prefix; [ | discriminate]. cbn in Hin.
    destruct Hin as [<- | []]. exists [p]. split; [constructor |].
    exact Havoid.
  - cbn in Heq. injection Heq as <- Htail.
    destruct Hin as [<- | Hin].
    + exists [first]. split; [constructor | cbn in *; tauto].
    + destruct (IHHpath prefix suffix member avoid Htail
        ltac:(cbn in Havoid; tauto) Hin) as [before_member [Hp Hnot]].
      exists (first :: before_member). split.
      * eapply point_path_prepend; eassumption.
      * cbn in *. tauto.
Qed.

(* Mutual domination of reachable points means they are the same point.
   Reachability prevents unreachable graph fragments making this vacuous. *)
Theorem point_dominance_antisymmetric : forall (entry : block)
    (lhs rhs : point),
  point_reachable entry rhs -> point_dominates entry lhs rhs ->
  point_dominates entry rhs lhs -> lhs = rhs.
Proof.
  intros entry lhs rhs [points Hpath] Hlhs Hrhs.
  destruct (point_eqb lhs rhs) eqn:E;
    [apply point_eqb_spec; exact E |].
  destruct (point_path_first_visit _ _ _ Hpath)
    as [prefix [Hp Hnot]].
  pose proof (Hlhs _ Hp) as Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | [Heq | []]].
  - destruct (point_path_prefix_avoiding _ _ _ Hp prefix [rhs] lhs rhs
      eq_refl Hnot Hin) as [before_lhs [Hbefore Havoid]].
    exfalso. apply Havoid, Hrhs, Hbefore.
  - subst lhs. assert (point_eqb rhs rhs = true)
      by (apply point_eqb_spec; reflexivity). congruence.
Qed.

(* A dominator of a successor also dominates its predecessor unless it
   is the successor itself, where a definition may just have become live. *)
Lemma point_dominates_predecessor : forall (entry : block)
    (dominator before after : point),
  point_dominates entry dominator after -> dominator <> after ->
  point_edge before after -> point_dominates entry dominator before.
Proof.
  intros entry dominator before after Hdom Hneq Hedge points Hpath.
  pose proof (Hdom _ (point_path_snoc _ _ _ _ Hpath Hedge)) as Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | [Heq | []]];
    [exact Hin | congruence].
Qed.

(* A definition in another block that dominates this block's terminator
   also dominates its entry: advancing through the body never encounters
   that other definition. *)
Lemma other_block_dominates_entry : forall (entry b : block)
    (dominator : point),
  fst dominator <> b -> point_dominates entry dominator (b, 0%nat) ->
  point_dominates entry dominator (entry_point b).
Proof.
  intros entry b dominator Hother Hdom.
  assert (forall (remaining : nat), remaining <= length (block_body b) ->
    point_dominates entry dominator (b, remaining)) as Hthrough.
  { intros remaining. induction remaining as [ | remaining IH]; intros Hlen.
    - exact Hdom.
    - eapply point_dominates_predecessor.
      + apply IH. lia.
      + intros Heq. apply (f_equal fst) in Heq. cbn in Heq. contradiction.
      + constructor. lia. }
  apply Hthrough. lia.
Qed.

(* A visited point has a prefix path contained in the original path. *)
Lemma point_path_member : forall (first last : point) (points : list point),
  point_path first points last -> forall (member : point), In member points ->
  exists (prefix : list point), point_path first prefix member
    /\ forall (visited : point), In visited prefix -> In visited points.
Proof.
  intros first last points Hpath. induction Hpath; intros member Hin.
  - destruct Hin as [<- | []]. exists [p]. split; [constructor | auto].
  - destruct Hin as [<- | Hin].
    + exists [first]. split; [constructor | cbn; tauto].
    + destruct (IHHpath member Hin) as [prefix [Hp Hmembers]].
      exists (first :: prefix). split.
      * eapply point_path_prepend; eassumption.
      * intros visited [<- | Hvisited]; [left; reflexivity |].
        right. apply Hmembers. exact Hvisited.
Qed.

(* Dominating a dominator is enough to dominate its target. *)
Theorem point_dominance_transitive : forall (entry : block)
    (first middle last : point),
  point_dominates entry first middle -> point_dominates entry middle last ->
  point_dominates entry first last.
Proof.
  intros entry first middle last Hfirst Hmiddle points Hpath.
  destruct (point_path_member _ _ _ Hpath middle (Hmiddle _ Hpath))
    as [prefix [Hprefix Hmembers]].
  apply Hmembers, Hfirst, Hprefix.
Qed.

(* A block path can be extended by one incoming edge. *)
Lemma path_prepend : forall (first next last : block) (blocks : list block),
  In first (predecessors next) -> path next blocks last ->
  path first (first :: blocks) last.
Proof.
  intros first next last blocks Hedge Hpath.
  inversion Hpath; subst; apply path_cons; assumption.
Qed.

(* Project a program-point path to a block path. Every block other than
   the starting block was entered at its full-body entry point. *)
Lemma point_path_blocks : control_edges -> forall (first last : point)
    (points : list point),
  point_path first points last ->
  exists (blocks : list block), path (fst first) blocks (fst last)
    /\ forall (b : block), In b blocks ->
         b = fst first \/ In (entry_point b) points.
Proof.
  intros Hedges first last points Hpath. induction Hpath.
  - exists [fst p]. split; [constructor |].
    intros b [<- | []]. left. reflexivity.
  - destruct IHHpath as [blocks [Hblocks Hmembers]].
    destruct H; cbn in *.
    + exists blocks. split; [exact Hblocks |].
      intros block Hblock. destruct (Hmembers block Hblock) as [Hfirst | Hin].
      * left. exact Hfirst.
      * right. right. exact Hin.
    + exists (source :: blocks). split.
      * eapply path_prepend; [ | exact Hblocks].
        apply (proj2 (predecessor_successor Hedges source target)). exact H.
      * intros block [<- | Hblock]; [left; reflexivity |].
        destruct (Hmembers block Hblock) as [-> | Hin].
        -- right. right. left. reflexivity.
        -- right. right. exact Hin.
Qed.

(* Semantic block dominance lifts to dominance of the block's entry
   point, preserving within-block instruction ordering. *)
Theorem point_dominance_of_block : control_edges -> forall (entry : block)
    (dominator : block) (target : point),
  (forall (blocks : list block), path entry blocks (fst target) ->
     In dominator blocks) ->
  point_dominates entry (entry_point dominator) target.
Proof.
  intros Hedges entry dominator target Hdom points Hpath.
  destruct (point_path_blocks Hedges _ _ _ Hpath)
    as [blocks [Hblocks Hmembers]].
  destruct (Hmembers dominator (Hdom blocks Hblocks)) as [Heq | Hin];
    [ | exact Hin].
  cbn in Heq. subst dominator. inversion Hpath; subst; left; reflexivity.
Qed.

(* A path contains its endpoint. *)
Lemma path_last : forall (first : block) (p : list block) (last : block),
  path first p last -> In last p.
Proof.
  intros first p last H. induction H; cbn; auto.
Qed.

(* Following one more edge extends a path at its end. *)
Lemma path_snoc :
  forall (first : block) (p : list block) (last next : block),
  path first p last -> In last (predecessors next) ->
  path first (p ++ [next]) next.
Proof.
  intros first p last next H. induction H; intros Hedge; cbn.
  - apply path_cons; [exact Hedge | constructor].
  - apply path_cons; [assumption | apply IHpath; exact Hedge].
Qed.

(* A path that visits [succ], without starting there, arrives over the
   edge from [succ]'s only predecessor. *)
Lemma path_edge_to :
  forall (first : block) (p : list block) (last succ pred : block),
  path first p last -> In succ p -> first <> succ ->
  predecessors succ = [pred] ->
  edge_on p pred succ.
Proof.
  intros a p c succ src Hp.
  induction Hp as [ b | a b l c Hab Hp IH ]; intros Hin Hne Hpred.
  - destruct Hin as [ -> | [] ]. contradiction.
  - destruct (block_eqb b succ) eqn:E.
    + apply block_eqb_spec in E. subst b.
      rewrite Hpred in Hab. destruct Hab as [ -> | [] ].
      exists [], l. reflexivity.
    + assert (Hne' : b <> succ).
      { intros ->. rewrite block_eqb_refl in E. discriminate. }
      destruct Hin as [ -> | Hin ]; [ contradiction | ].
      destruct (IH Hin Hne' Hpred) as [l1 [l2 Heq]].
      exists (a :: l1), l2. rewrite Heq. reflexivity.
Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

Section Dominance.
  Variable entry : block.
  Hypothesis dominance : dominance_semantics entry.

  (* When [succ] dominates [target] and [pred] is its sole predecessor,
     every path from the entry to [target] takes the edge [pred -> succ]. *)
  Theorem edge_on_every_path : forall (pred succ target : block),
    succ --dom--> target -> sole_predecessor pred succ = true ->
    forall (p : list block), path entry p target -> edge_on p pred succ.
  Proof.
    intros pred succ target Hd H p Hp. unfold sole_predecessor in H.
    apply andb_true_iff in H. destruct H as [Hnd Hpred].
    destruct (predecessors succ) as [ | p0 [ | ? ? ] ] eqn:Hps;
      try discriminate.
    apply block_eqb_spec in Hpred. subst p0.
    apply (path_edge_to entry p target succ pred Hp).
    - exact (dominance.(dominates_spec) succ target Hd p Hp).
    - intros ->. rewrite dominance.(entry_dominates) in Hnd. discriminate.
    - exact Hps.
  Qed.
End Dominance.
