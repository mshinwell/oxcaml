(* Which loops to delete: [find_deletions], which combines the analyses of
   NaturalLoop.v, InductionVar.v, LoopTermination.v and DeadInductionVar.v
   into the decision. The extraction of this file, DeleteEmptyLoops.ml, is
   the implementation; delete_empty_loops.ml in the parent directory wraps
   it, builds the table of [Ssa_view.compute_op_def] it is given, and
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
    (fun bl =>
      forallb (fun s => set_mem s loop.(body) || block_eqb s exit)
        (all_successors bl))
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
   block list and the table of [Ssa_view.compute_op_def]. *)
Definition find_deletions (op_def : op_def) (blocks : list block)
    : list (block * block) :=
  let loops := InductionVar.analyze op_def blocks in
  let dead := DeadInductionVar.analyze blocks loops in
  filter_map
    (fun dr =>
      let loop := dr.(loop) in
      let bivs := map (fun br => br.(biv)) dr.(bivs) in
      if dr.(useless) && body_effect_free loop
         && acyclic_except blocks loop.(body) loop.(header)
      then
        match find_exit_branch loop with
        | Some exit_info =>
          match params exit_info.(exit_target) with
          | [] =>
            if single_exit loop exit_info.(exit_target)
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

Definition body_does_nothing (l : natural_loop) : Prop :=
  forall bl, set_mem bl l.(body) = true -> block_does_nothing bl.

(* Every edge out of a block of the body stays in the body or goes to
   [exit]. *)
Definition exits_only_to (l : natural_loop) (exit : block) : Prop :=
  forall bl, set_mem bl l.(body) = true ->
    forall s, In s (all_successors bl) ->
      set_mem s l.(body) = true \/ s = exit.

(* The header's exit branch, in the shape LoopTermination.v recognises,
   goes to [exit], which takes no arguments. *)
Definition exit_branch_to (l : natural_loop) (exit : block) : Prop :=
  exists exit_info,
    find_exit_branch l = Some exit_info
    /\ exit_info.(exit_target) = exit /\ params exit = [].

Definition no_infinite_header_run (op_def : op_def) (l : natural_loop)
    : Prop :=
  forall iter, infinite_header_run op_def l iter -> False.

(* Every parameter of the header is one of [bivs], and each of those is a
   basic induction variable of [l] that is dead. *)
Definition params_are_dead_bivs (op_def : op_def) (blocks : list block)
    (l : natural_loop) (bivs : list InductionVar.biv) : Prop :=
  (forall k v, nth_int (params l.(header)) k = Some v ->
     exists b, In b bivs /\ b.(param_index) = k)
  /\ (forall b, In b bivs -> biv_spec op_def l b /\ dead_spec blocks b).

(* What holds of a loop [l], with the basic induction variables [bivs]
   InductionVar.v reports for it, when [find_deletions] deletes it. *)
Definition deletable (op_def : op_def) (blocks : list block)
    (l : natural_loop) (bivs : list InductionVar.biv) (exit : block)
    : Prop :=
  exit_branch_to l exit
  /\ no_infinite_header_run op_def l
  /\ no_infinite_path_except l.(body) l.(header)
  /\ params_are_dead_bivs op_def blocks l bivs
  /\ body_does_nothing l
  /\ exits_only_to l exit.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* What [body_effect_free] checks, read back. *)
Lemma body_effect_free_spec : forall l,
  body_effect_free l = true -> body_does_nothing l.
Proof.
  intros l H bl Hbl. unfold body_effect_free in H.
  rewrite set_for_all_spec in H. apply block_effect_free_spec, H. exact Hbl.
Qed.

(* What [single_exit] checks, read back. *)
Lemma single_exit_spec : forall l exit,
  single_exit l exit = true -> exits_only_to l exit.
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

Theorem find_deletions_spec : forall op_def blocks h exit,
  In (h, exit) (find_deletions op_def blocks) ->
  exists l bivs,
    In (l, bivs) (InductionVar.analyze op_def blocks)
    /\ h = l.(header)
    /\ deletable op_def blocks l bivs exit.
Proof.
  intros op_def blocks h exit H. unfold find_deletions in H. cbv zeta in H.
  apply filter_map_In in H. destruct H as [dr [Hdr H]].
  destruct (DeadInductionVar.analyze_spec _ _ _ Hdr) as [Hin [Hbivs Huseless]].
  cbv zeta in H.
  destruct (dr.(useless) && body_effect_free dr.(loop)
    && acyclic_except blocks dr.(loop).(body) dr.(loop).(header)) eqn:Hcond;
    [ | discriminate ].
  apply andb_true_iff in Hcond. destruct Hcond as [Hcond Hacyclic].
  apply andb_true_iff in Hcond. destruct Hcond as [Hu Hfree].
  destruct (find_exit_branch dr.(loop)) as [exit_info | ] eqn:Hexit;
    [ | discriminate ].
  destruct (params exit_info.(exit_target)) eqn:Hparams; [ | discriminate ].
  destruct (single_exit dr.(loop) exit_info.(exit_target) && _) eqn:Hcond;
    [ | discriminate ].
  apply andb_true_iff in Hcond. destruct Hcond as [Hsingle Hterm].
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
  - unfold no_infinite_header_run. intros iter Hrun.
    exact (analyze_Terminates_of_graph _ _ _ Hrun _ _ Hin Hanalyze).
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
