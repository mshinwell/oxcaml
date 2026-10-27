(* The basic induction variables a loop computes for nothing but its own
   control: used only by the exit comparison and their own updates, with
   the comparison used only by the header's branch. The extraction of this
   file, DeadInductionVar.ml, is the implementation.

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary, SsaModel.v for how the models see an SSA graph, SsaGraph.v
   (backend/ssa/rocq/) for the uses of a value in the graph, and
   NaturalLoop.v and InductionVar.v for the loops, their exit branches and
   the basic induction variables this file is given. As there, the file has
   four parts: (1) the definitions, (2) the intended meaning, (3)
   stepping-stone lemmas, (4) the theorems. Parts 1 and 2 are the part to
   check by eye.

   Why the uses of the exit comparison are checked ([cond_uses_ok]): deleting
   the loop (DeleteEmptyLoops.v) leaves the comparison computed from the
   loop's initial parameters, so a use of it other than the header's
   branch -- an instruction, or a [Return] of it after the loop -- would
   observe a value the iteration that ended the loop did not produce. The
   first version of the analysis did not check this; the error was found
   while writing the model.

   The result, in part 4, is [analyze_spec]: for each basic induction
   variable reported dead, [dead_spec] (part 2) holds, which spells out
   what was checked of every instruction and terminator of the
   graph: the parameter is used only by the exit comparison and its own
   updates, the exit comparison only by the header's branch, and each
   update only by the exit comparison and as that parameter's argument of
   its back edge's [Goto]; and that a loop reported useless has every
   header parameter among its dead induction variables. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlOption OxCamlInt OxCamlList.
From OxCamlSsa Require Import SsaModel SsaGraph.
From OxCamlLoop Require Import NaturalLoop InductionVar.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

(* A BIV with its verdict, and a loop with its BIVs' verdicts and whether
   every header parameter is a dead BIV. After these, the type [biv] of
   InductionVar.v is written [InductionVar.biv], its field [loop]
   [InductionVar.loop]. *)
Record biv_result : Type :=
  { biv : biv;
    dead : bool }.

Record loop_result : Type :=
  { loop : natural_loop;
    bivs : list biv_result;
    useless : bool }.

(* The parameter [k] of [header] is read only by the exit comparison
   [cond] and by the [updates], and by no terminator. *)
Definition param_uses_ok (blocks : list block) (header : block) (k : int)
    (cond : value) (updates : list value) : bool :=
  all_uses_ok blocks (is_param header k)
    (fun i =>
      instr_defines_value i cond || existsb (instr_defines_value i) updates)
    (fun _ _ => false).

(* The exit comparison is read by no instruction, and by no terminator but
   the header's. *)
Definition cond_uses_ok (blocks : list block) (header : block) (cond : value)
    : bool :=
  all_uses_ok blocks (value_eqb cond)
    (fun _ => false)
    (fun bl _ => block_eqb bl header).

(* The update value [u] is read by no instruction but the exit comparison,
   and by no terminator but the [Goto] to the header of a back-edge block
   (one of [back_preds]), as the argument at position [k] and at no other
   position. *)
Definition update_uses_ok (blocks : list block) (header : block)
    (back_preds : blockset) (k : int) (cond u : value) : bool :=
  all_uses_ok blocks (value_eqb u)
    (fun i => instr_defines_value i cond)
    (fun bl _ => set_mem bl back_preds && goto_passes header k u bl).

(* Whether a BIV is dead: its parameter, the exit comparison and its update
   values are used only as the loop's own control requires, as [dead_spec]
   (part 2) spells out. *)
Definition is_dead (blocks : list block) (biv : InductionVar.biv) : bool :=
  match find_exit_branch biv.(InductionVar.loop) with
  | None => false
  | Some exit_info =>
    let cond := exit_info.(condition) in
    let header := biv.(InductionVar.loop).(header) in
    let k := biv.(param_index) in
    let back_preds := back_edge_set biv.(InductionVar.loop) in
    param_uses_ok blocks header k cond biv.(update)
    && cond_uses_ok blocks header cond
    && forallb (update_uses_ok blocks header back_preds k cond) biv.(update)
  end.

(* Every header parameter is a dead BIV. *)
Definition loop_is_useless (loop : natural_loop) (bivs : list biv_result)
    : bool :=
  same_length (params loop.(header)) bivs && forallb dead bivs.

(* The verdicts for each loop given, with its BIVs. *)
Definition analyze (blocks : list block)
    (loops : list (natural_loop * list InductionVar.biv))
    : list loop_result :=
  map
    (fun '(loop, bivs) =>
      let bivs :=
        map (fun biv => {| biv := biv; dead := is_dead blocks biv |}) bivs
      in
      {| loop := loop; bivs := bivs; useless := loop_is_useless loop bivs |})
    loops.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

(* What [dead = true] establishes of a basic induction variable [b] of a
   loop with the exit branch [exit_info], in terms of [uses_only]
   (SsaGraph.v): its parameter is used only by the exit comparison and its
   own updates and by no terminator; the exit comparison is used by no
   instruction and only by the header's terminator; and each update value
   is used by no instruction but the exit comparison, and by no terminator
   but the [Goto] to the header of a back-edge block, as the argument at
   the parameter's position and at no other ([passes_at]). *)
Definition param_used_only_by_exit_and_updates (blocks : list block)
    (header : block) (k : int) (cond : value) (updates : list value) : Prop :=
  uses_only blocks (is_param header k)
    (fun i =>
      instr_defines_value i cond = true
      \/ exists u, In u updates /\ instr_defines_value i u = true)
    (fun _ _ => False).

Definition cond_used_only_by_header_branch (blocks : list block)
    (header : block) (cond : value) : Prop :=
  uses_only blocks (value_eqb cond) (fun _ => False) (fun bl _ => bl = header).

Definition update_used_only_by_exit_and_back_edge (blocks : list block)
    (l : natural_loop) (k : int) (cond u : value) : Prop :=
  uses_only blocks (value_eqb u)
    (fun i => instr_defines_value i cond = true)
    (fun bl _ => In bl l.(back_edges) /\ passes_at l.(header) k u bl).

Definition dead_spec (blocks : list block) (b : InductionVar.biv) : Prop :=
  exists exit_info,
    find_exit_branch b.(InductionVar.loop) = Some exit_info
    /\ let cond := exit_info.(condition) in
       let l := b.(InductionVar.loop) in
       let k := b.(param_index) in
       param_used_only_by_exit_and_updates blocks l.(header) k cond b.(update)
       /\ cond_used_only_by_header_branch blocks l.(header) cond
       /\ forall u, In u b.(update) ->
            update_used_only_by_exit_and_back_edge blocks l k cond u.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* The approval [update_uses_ok] asks of a terminator use, read back. *)
Lemma update_term_approved : forall l header k v bl,
  set_mem bl (back_edge_set l) && goto_passes header k v bl = true ->
  In bl l.(back_edges) /\ passes_at header k v bl.
Proof.
  intros l header k v bl H. apply andb_true_iff in H. destruct H as [Hset H].
  split; [ apply back_edge_set_spec; exact Hset | ].
  apply goto_passes_spec. exact H.
Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

(* A BIV [is_dead] accepts satisfies [dead_spec]. *)
Theorem is_dead_spec : forall blocks b,
  is_dead blocks b = true -> dead_spec blocks b.
Proof.
  intros blocks b H. unfold is_dead in H.
  destruct (find_exit_branch b.(InductionVar.loop)) as [exit_info | ]
    eqn:Hexit; [ | discriminate ].
  cbv zeta in H.
  apply andb_true_iff in H. destruct H as [H Hupd].
  apply andb_true_iff in H. destruct H as [Hself Hcond].
  rewrite forallb_forall in Hupd.
  exists exit_info. split; [ exact Hexit | ]. cbv zeta.
  split; [ | split ].
  - unfold param_uses_ok in Hself. apply all_uses_ok_spec in Hself.
    unfold param_used_only_by_exit_and_updates.
    refine (uses_only_weaken _ _ _ _ _ _ _ _ Hself).
    + intros i Hi. apply orb_true_iff in Hi. destruct Hi as [Hi | Hi].
      * left. exact Hi.
      * right. apply existsb_exists in Hi. exact Hi.
    + intros bl arr Hf. discriminate.
  - unfold cond_uses_ok in Hcond. apply all_uses_ok_spec in Hcond.
    unfold cond_used_only_by_header_branch.
    refine (uses_only_weaken _ _ _ _ _ _ _ _ Hcond).
    + intros i Hi. discriminate.
    + intros bl arr Hbl. apply block_eqb_spec. exact Hbl.
  - intros u Hu. specialize (Hupd u Hu).
    unfold update_uses_ok in Hupd. apply all_uses_ok_spec in Hupd.
    unfold update_used_only_by_exit_and_back_edge.
    refine (uses_only_weaken _ _ _ _ _ _ _ _ Hupd).
    + intros i Hi. exact Hi.
    + intros bl arr Hbl. apply update_term_approved. exact Hbl.
Qed.

(* A loop [loop_is_useless] accepts has as many BIVs as its header has
   parameters, all of them dead. *)
Theorem loop_is_useless_spec : forall loop bivs,
  loop_is_useless loop bivs = true ->
  length (params loop.(header)) = length bivs
  /\ forall br, In br bivs -> br.(dead) = true.
Proof.
  intros loop bivs H. unfold loop_is_useless in H.
  apply andb_true_iff in H. destruct H as [Hlen Hdead].
  split; [ apply same_length_spec; exact Hlen | ].
  rewrite forallb_forall in Hdead. exact Hdead.
Qed.

(* Each loop result is for one of the loops given, its [bivs] are those
   of the loop with [dead] computed by [is_dead], every one reported dead
   satisfies [dead_spec], and a loop reported useless has as many dead
   induction variables as its header has parameters. *)
Theorem analyze_spec : forall blocks loops r,
  In r (analyze blocks loops) ->
  In (r.(loop), map biv r.(bivs)) loops
  /\ (forall br, In br r.(bivs) ->
        br.(dead) = is_dead blocks br.(biv)
        /\ (br.(dead) = true -> dead_spec blocks br.(biv)))
  /\ (r.(useless) = true ->
        length (params r.(loop).(header)) = length r.(bivs)
        /\ forall br, In br r.(bivs) -> br.(dead) = true).
Proof.
  intros blocks loops r H. unfold analyze in H.
  apply in_map_iff in H. destruct H as [[l bs] [<- Hin]]. cbv zeta.
  cbn [loop bivs useless].
  split; [ | split ].
  - rewrite map_map. cbn [biv]. rewrite map_id. exact Hin.
  - intros br Hbr. apply in_map_iff in Hbr. destruct Hbr as [b [<- Hb]].
    cbn [biv dead]. split; [ reflexivity | ].
    intros Hd. apply is_dead_spec. exact Hd.
  - intros Hu. apply loop_is_useless_spec. exact Hu.
Qed.
