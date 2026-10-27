(* Which loops to delete: [find_deletions], which combines the analyses of
   NaturalLoop.v, InductionVar.v, LoopTermination.v and DeadInductionVar.v
   into the decision. The extraction of this file, DeleteEmptyLoops.ml, is
   the implementation; delete_empty_loops.ml in the parent directory wraps
   it, builds the table of defining blocks ([op_def]) it is given, and
   rewrites the graph at the (header, exit target) pairs it returns ([run],
   over [Ssa_reducer]), which is not modelled.

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary and SsaModel.v for how the models see an SSA graph. As there,
   the file has four parts: (1) the definitions, (2) the intended meaning,
   (3) stepping-stone lemmas, (4) the theorems. Parts 1 and 2 are the part
   to check by eye.

   The result, in part 4, is [find_deletions_spec]: a loop is deleted only
   when [deletable] (part 2) holds of it. Its header's exit branch is the
   simple one LoopTermination.v recognises, with an exit target that takes
   no arguments; the loop has no run that visits its header for ever
   ([infinite_header_run] there), and no infinite path through its body
   avoiding the header; each of its header's parameters is a basic
   induction variable (InductionVar.v) that is dead in the sense of
   DeadInductionVar.v; every block of its body has only side-effect-free
   instructions and a [Goto] or [Switch] terminator; and that exit edge is
   the only edge leaving the body. That is what justifies replacing the
   header's branch by a jump to the exit target: the loop always reaches
   that exit, can be left no other way, and computes nothing that is
   observed after it.

   The last point also covers the header's own instructions, which still
   run once after the rewrite, as they did on the first iteration before
   it. Being free of side effects, they can only be observed through a
   value used after the loop. By SSA scoping no block of the body but the
   header dominates the exit, so such a value is a header parameter, which
   DeadInductionVar.v forbids any use of outside the loop's own control, or
   is defined by a header instruction, whose inputs are values defined
   before the loop, loads from memory the loop does not write, or header
   parameters; and a parameter used by an instruction other than the exit
   comparison and its own update is not dead, which keeps the loop. So
   every such value is the same at every iteration, the one after the
   rewrite included. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlOption OxCamlInt OxCamlList.
From OxCamlSsa Require Import SsaModel SsaGraph.
From OxCamlLoop Require Import NaturalLoop InductionVar LoopTermination
  DeadInductionVar.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

(* Every block of the body is [block_effect_free] (SsaGraph.v): its
   instructions have no side effects and its terminator only transfers
   control within the function. *)
Definition body_effect_free (loop : natural_loop) : bool :=
  set_for_all block_effect_free loop.(body).

(* Every edge out of a block of the body stays in the body or is the
   header's exit edge, to [exit]. [body_effect_free] only sees the blocks
   of the body: a [Switch] or [Goto] from the body to a block outside it
   (a raise, a return of another value, ...) would leave the loop before
   the header's test fails, and somewhere other than [exit]. *)
Definition single_exit (loop : natural_loop) (exit : block) : bool :=
  set_for_all
    (fun block =>
      forallb (fun succ => set_mem succ loop.(body) || block_eqb succ exit)
        (all_successors block))
    loop.(body).

(* [LoopTermination.analyze] as a boolean. It is the costly check, so
   [find_deletions] runs it last, once the others have passed. *)
Definition loop_terminates (op_def : op_def) (bivs : list InductionVar.biv)
    : bool :=
  match LoopTermination.analyze op_def bivs with
  | Terminates => true
  | Unknown => false
  end.

(* The loops to delete, as (header, exit target) pairs, given the graph's
   block list and the table of defining blocks. *)
Definition find_deletions (op_def : op_def) (blocks : list block)
    : list (block * block) :=
  let loops := InductionVar.analyze op_def blocks in
  let dead := DeadInductionVar.analyze blocks loops in
  filter_map
    (fun result =>
      let loop := result.(loop) in
      let bivs := map (fun biv_result => biv_result.(biv)) result.(bivs) in
      if result.(useless) && body_effect_free loop
      then
        match find_exit_branch loop with
        | Some exit_info =>
          match params exit_info.(exit_target) with
          | [] =>
            if single_exit loop exit_info.(exit_target)
               && acyclic_except blocks loop.(body) loop.(header)
               && loop_terminates op_def bivs
            then Some (loop.(header), exit_info.(exit_target))
            else None
          | _ :: _ => None
          end
        | None => None
        end
      else None)
    dead.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

Definition body_does_nothing (loop : natural_loop) : Prop :=
  forall (block : block),
    set_mem block loop.(body) = true -> block_does_nothing block.

(* Every edge out of a block of the body stays in the body or goes to
   [exit]. *)
Definition exits_only_to (loop : natural_loop) (exit : block) : Prop :=
  forall (pred : block), set_mem pred loop.(body) = true ->
    forall (succ : block), In succ (all_successors pred) ->
      set_mem succ loop.(body) = true \/ succ = exit.

(* The header's exit branch, in the shape LoopTermination.v recognises,
   goes to [exit], which takes no arguments. *)
Definition exit_branch_to (loop : natural_loop) (exit : block) : Prop :=
  exists exit_info,
    find_exit_branch loop = Some exit_info
    /\ exit_info.(exit_target) = exit /\ params exit = [].

(* No run of [loop] goes on for ever (LoopTermination.v), whatever the
   graph's entry block. *)
Definition no_infinite_header_run (op_def : op_def) (loop : natural_loop)
    : Prop :=
  forall (entry : block) (iter : nat -> value -> Z),
    infinite_header_run entry op_def loop iter -> False.

(* Every parameter of the header is one of [bivs], and each of those is a
   basic induction variable of [loop] that is dead. *)
Definition params_are_dead_bivs (op_def : op_def) (blocks : list block)
    (loop : natural_loop) (bivs : list InductionVar.biv) : Prop :=
  (forall (k : int) (v : value), nth_int (params loop.(header)) k = Some v ->
     exists biv, In biv bivs /\ biv.(param_index) = k)
  /\ (forall (biv : InductionVar.biv), In biv bivs ->
        biv_spec op_def loop biv /\ dead_spec blocks biv).

(* What holds of a loop [loop], with the basic induction variables [bivs]
   InductionVar.v reports for it, when [find_deletions] deletes it. *)
Definition deletable (op_def : op_def) (blocks : list block)
    (loop : natural_loop) (bivs : list InductionVar.biv) (exit : block)
    : Prop :=
  exit_branch_to loop exit
  /\ no_infinite_header_run op_def loop
  /\ no_infinite_path_except loop.(body) loop.(header)
  /\ params_are_dead_bivs op_def blocks loop bivs
  /\ body_does_nothing loop
  /\ exits_only_to loop exit.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* What [body_effect_free] checks, read back. *)
Lemma body_effect_free_spec : forall (loop : natural_loop),
  body_effect_free loop = true -> body_does_nothing loop.
Proof.
  intros l H bl Hbl. unfold body_effect_free in H.
  rewrite set_for_all_spec in H. apply block_effect_free_spec, H. exact Hbl.
Qed.

(* What [single_exit] checks, read back. *)
Lemma single_exit_spec : forall (loop : natural_loop) (exit : block),
  single_exit loop exit = true -> exits_only_to loop exit.
Proof.
  intros l exit H bl Hbl s Hs. unfold single_exit in H.
  rewrite set_for_all_spec in H. specialize (H bl Hbl).
  rewrite forallb_forall in H. specialize (H s Hs).
  apply orb_true_iff in H. destruct H as [H | H]; [ left; exact H | ].
  right. apply block_eqb_spec. exact H.
Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

Theorem find_deletions_spec :
  forall (op_def : op_def) (blocks : list block) (header exit : block),
  In (header, exit) (find_deletions op_def blocks) ->
  exists loop bivs,
    In (loop, bivs) (InductionVar.analyze op_def blocks)
    /\ header = loop.(NaturalLoop.header)
    /\ deletable op_def blocks loop bivs exit.
Proof.
  intros op_def blocks h exit H. unfold find_deletions in H. cbv zeta in H.
  apply filter_map_In in H. destruct H as [dr [Hdr H]].
  destruct (DeadInductionVar.analyze_spec _ _ _ Hdr) as [Hin [Hbivs Huseless]].
  cbv zeta in H.
  destruct (dr.(useless) && body_effect_free dr.(loop)) eqn:Hcond;
    [ | discriminate ].
  apply andb_true_iff in Hcond. destruct Hcond as [Hu Hfree].
  destruct (find_exit_branch dr.(loop)) as [exit_info | ] eqn:Hexit;
    [ | discriminate ].
  destruct (params exit_info.(exit_target)) eqn:Hparams; [ | discriminate ].
  destruct (single_exit dr.(loop) exit_info.(exit_target) && _ && _)
    eqn:Hcond; [ | discriminate ].
  apply andb_true_iff in Hcond. destruct Hcond as [Hcond Hterm].
  apply andb_true_iff in Hcond. destruct Hcond as [Hsingle Hacyclic].
  unfold loop_terminates in Hterm.
  destruct (LoopTermination.analyze op_def _) eqn:Hanalyze;
    [ | discriminate ].
  injection H as <- <-.
  exists dr.(loop), (map biv dr.(bivs)).
  split; [ exact Hin | split; [ reflexivity | ] ].
  destruct (InductionVar.analyze_spec _ _ _ _ Hin) as [_ [Hdef Hspec]].
  destruct (Huseless Hu) as [Hlen Hdead].
  unfold deletable.
  split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - unfold exit_branch_to. exists exit_info.
    split; [ exact Hexit | split; [ reflexivity | exact Hparams ] ].
  - unfold no_infinite_header_run. intros entry iter Hrun.
    exact (analyze_Terminates_of_graph _ _ _ _ Hrun _ _ Hin Hanalyze).
  - apply (acyclic_except_sound blocks). exact Hacyclic.
  - unfold params_are_dead_bivs. split.
    + intros k v Hk. rewrite Hdef.
      apply (analyze_loop_cover _ _ _ v); [ | exact Hk ].
      rewrite <- Hdef, length_map. symmetry. exact Hlen.
    + intros b Hb. split; [ apply Hspec; exact Hb | ].
      apply in_map_iff in Hb. destruct Hb as [br [<- Hbr]].
      destruct (Hbivs br Hbr) as [_ Hd]. apply Hd, Hdead. exact Hbr.
  - apply body_effect_free_spec. exact Hfree.
  - apply single_exit_spec. exact Hsingle.
Qed.
