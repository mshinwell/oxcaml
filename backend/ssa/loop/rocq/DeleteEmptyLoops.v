(* Which loops to delete: [find_deletions], which combines the analyses of
   NaturalLoop.v, InductionVar.v, LoopTermination.v and DeadInductionVar.v
   into the decision. The extraction of this file, DeleteEmptyLoops.ml, is
   the implementation; delete_empty_loops.ml in the parent directory wraps
   it, builds the table of [Induction_var.compute_op_def] it is given, and
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
   ([infinite_run] there); each of its header's parameters is a basic
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
From OxCamlStdlib Require Import OcamlOption OcamlInt OcamlList.
From OxCamlSsa Require Import SsaModel.
From OxCamlLoop Require Import NaturalLoop InductionVar LoopTermination
  DeadInductionVar.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

(* A terminator that only transfers control within the function. *)
Definition terminator_pure_control (t : Terminator.t) : bool :=
  match t with
  | Terminator.Continue (Goto _) _ | Terminator.Switch _ _ => true
  | Terminator.Continue (Return | Raise _ | Unreachable) _
  | Terminator.Call _ | Terminator.Invalid _ => false
  end.

(* Every block of the body has only side-effect-free instructions and such
   a terminator. *)
Definition body_effect_free (loop : natural_loop) : bool :=
  set_for_all
    (fun bl =>
      forallb (fun i => negb (has_side_effect i)) (block_body bl)
      && terminator_pure_control (terminator bl))
    loop.(body).

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
   block list and the table of [Induction_var.compute_op_def]. *)
Definition find_deletions (op_def : op_def) (blocks : list block)
    : list (block * block) :=
  let loops := InductionVar.analyze op_def blocks in
  let dead := DeadInductionVar.analyze blocks loops in
  filter_map
    (fun dr =>
      let loop := dr.(loop) in
      let bivs := map (fun br => br.(biv)) dr.(bivs) in
      if dr.(useless) && body_effect_free loop
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

(* Every block of the body has only side-effect-free instructions and a
   terminator that stays within the function. *)
Definition body_does_nothing (l : natural_loop) : Prop :=
  forall bl, set_mem bl l.(body) = true ->
    (forall i, In i (block_body bl) -> has_side_effect i = false)
    /\ terminator_pure_control (terminator bl) = true.

(* Every edge out of a block of the body stays in the body or goes to
   [exit]. *)
Definition leaves_only_to (l : natural_loop) (exit : block) : Prop :=
  forall bl, set_mem bl l.(body) = true ->
    forall s, In s (all_successors bl) -> set_mem s l.(body) = true \/ s = exit.

(* What holds of a loop [l], with the basic induction variables [bivs]
   InductionVar.v reports for it, when [find_deletions] deletes it. *)
Definition deletable (op_def : op_def) (blocks : list block)
    (l : natural_loop) (bivs : list InductionVar.biv) (exit : block)
    : Prop :=
  (* the exit branch, whose target takes no arguments *)
  (exists exit_info,
     find_exit_branch l = Some exit_info
     /\ exit_info.(exit_target) = exit /\ params exit = [])
  (* no run of the loop visits the header for ever *)
  /\ (forall iter, infinite_run op_def l iter -> False)
  (* every header parameter is a dead basic induction variable *)
  /\ length (params l.(header)) = length bivs
  /\ (forall b, In b bivs -> biv_spec op_def l b /\ dead_spec blocks b)
  (* the body does nothing observable ... *)
  /\ body_does_nothing l
  (* ... and can only be left through the exit *)
  /\ leaves_only_to l exit.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

Lemma body_effect_free_spec : forall l,
  body_effect_free l = true -> body_does_nothing l.
Proof.
  intros l H bl Hbl. unfold body_effect_free in H.
  rewrite set_for_all_spec in H. specialize (H bl Hbl).
  apply andb_true_iff in H. destruct H as [Hi Ht].
  split; [ | exact Ht ].
  rewrite forallb_forall in Hi. intros i Hin.
  specialize (Hi i Hin). apply negb_true_iff in Hi. exact Hi.
Qed.

Lemma single_exit_spec : forall l exit,
  single_exit l exit = true -> leaves_only_to l exit.
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
  destruct (dr.(useless) && body_effect_free dr.(loop)) eqn:Hcond;
    [ | discriminate ].
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
  destruct (InductionVar.analyze_spec _ _ _ _ Hin) as [_ [_ Hspec]].
  destruct (Huseless Hu) as [Hlen Hdead].
  unfold deletable. split; [ | split; [ | split; [ | split; [ | split ] ] ] ].
  - exists exit_info. split; [ exact Hexit | split; [ reflexivity | ] ].
    exact Hparams.
  - intros iter Hrun.
    exact (analyze_Terminates_of_graph _ _ _ Hrun _ _ Hin Hanalyze).
  - rewrite length_map. exact Hlen.
  - intros b Hb. split; [ apply Hspec; exact Hb | ].
    apply in_map_iff in Hb. destruct Hb as [br [<- Hbr]].
    destruct (Hbivs br Hbr) as [_ Hd]. apply Hd, Hdead. exact Hbr.
  - apply body_effect_free_spec. exact Hfree.
  - apply single_exit_spec. exact Hsingle.
Qed.
