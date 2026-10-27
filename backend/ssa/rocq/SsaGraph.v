(* Properties of the blocks, terminators, instructions and values of an SSA
   graph that any pass may ask about, computed on the graph as SsaModel.v
   sees it:
   what a terminator does, what an instruction or a terminator reads, which
   values a block's [Goto] passes, whether every use of a value in the
   graph is approved, and whether a region is acyclic after removing one
   block. The extraction of this file, SsaGraph.ml, is the implementation.

   See the reading guide at the top of backend/ssa/loop/rocq/
   LoopComparisons.v for the Rocq vocabulary and SsaModel.v for how the
   models see an SSA graph. As there, the file has four parts: (1) the
   definitions, (2) the intended meaning, (3) stepping-stone lemmas, (4)
   the theorems. Parts 1 and 2 are the part to check by eye.

   The arguments of instructions and terminators, and a block's parameters,
   are lists here, indexed by [nth_int] (OxCamlList.v).

   The theorems of part 4 read each boolean check of part 1 back as its
   meaning in part 2. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxCamlStdlib Require Import OxCamlOption OxCamlInt OxCamlList.
From OxCamlBackend Require Import Operation.
From OxCamlSsa Require Import SsaModel.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

Local Open Scope sint63_scope.

(* A terminator that only transfers control within the function. *)
Definition terminator_pure_control (t : Terminator.t) : bool :=
  match t with
  | Terminator.Continue (Goto _) _ | Terminator.Switch _ _ => true
  | Terminator.Continue (Return | Raise _ | Unreachable) _
  | Terminator.Call _ | Terminator.Invalid _ => false
  end.

(* A block whose instructions have no side effects and whose terminator
   only transfers control within the function: running it has no effect
   beyond the values it defines. *)
Definition block_effect_free (bl : block) : bool :=
  forallb (fun i => negb (has_side_effect i)) (block_body bl)
  && terminator_pure_control (terminator bl).

(* [v] is parameter [index] of [bl]. *)
Definition is_param (bl : block) (index : int) (v : value) : bool :=
  value_eqb v (param bl index).

(* [i] is the instruction defining [v]. *)
Definition instr_defines_value (i : instr) (v : value) : bool :=
  match i, v with
  | Op id _, Res id' _ _ _ => instr_id_eqb id id'
  | _, _ => false
  end.

(* The values an instruction reads. *)
Definition args_of_instr (i : instr) : list value :=
  match i with
  | Op _ args => args
  | Push_trap | Pop_trap => []
  end.

(* The values a terminator reads, one list per kind of use: the arguments
   a [Continue] passes, the index of a [Switch], the arguments of a [Call]
   or an [Invalid]. *)
Definition terminator_args (term : Terminator.t) : list (list value) :=
  match term with
  | Terminator.Continue _ args =>
    [filter_map
       (fun arg =>
         match arg with
         | Terminator.Arg v => Some v
         | Terminator.Omitted_since_unused => None
         end)
       args]
  | Terminator.Switch index _ => [[index]]
  | Terminator.Call args => [args]
  | Terminator.Invalid args => [args]
  end.

(* [arg] passes the value [v]. *)
Definition arg_is (v : value) (arg : Terminator.arg) : bool :=
  match arg with
  | Terminator.Arg a => value_eqb a v
  | Terminator.Omitted_since_unused => false
  end.

(* The value an argument at position [index] passes, if any. *)
Definition arg_value (args : list Terminator.arg) (index : int)
    : option value :=
  match nth_int args index with
  | Some (Terminator.Arg v) => Some v
  | Some Terminator.Omitted_since_unused | None => None
  end.

(* The arguments [pred] passes to [target], when its terminator is a
   [Goto] there with one argument per parameter. *)
Definition goto_args (target pred : block) : option (list Terminator.arg) :=
  match terminator pred with
  | Terminator.Continue (Goto goto) args =>
    if block_eqb goto target && same_length args (params target)
    then Some args
    else None
  | _ => None
  end.

(* The terminator of [bl] is a [Goto] to [target] passing [v] as the
   argument at position [k], and at no other position. *)
Definition goto_passes (target : block) (k : int) (v : value) (bl : block)
    : bool :=
  match terminator bl with
  | Terminator.Continue (Goto goto) args =>
    block_eqb goto target
    && (match arg_value args k with
        | Some a => value_eqb a v
        | None => false
        end)
    && (count_occurrences (arg_is v) args =? one)
  | Terminator.Continue (Return | Raise _ | Unreachable) _
  | Terminator.Switch _ _ | Terminator.Call _ | Terminator.Invalid _ => false
  end.

(* Every use in the graph of a value [same] accepts is approved: by
   [approve_instr] for an instruction reading it, by [approve_term] for
   the block whose terminator reads it, given the list it is read in. *)
Definition all_uses_ok (blocks : list block) (same : value -> bool)
    (approve_instr : instr -> bool)
    (approve_term : block -> list value -> bool) : bool :=
  forallb
    (fun bl =>
      forallb
        (fun i => negb (existsb same (args_of_instr i)) || approve_instr i)
        (block_body bl)
      && forallb
           (fun arr => negb (existsb same arr) || approve_term bl arr)
           (terminator_args (terminator bl)))
    blocks.

(* Visit roots from left to right, threading the completed set. *)
Fixpoint visit_all (visit : blockset -> block -> option blockset)
    (seen : blockset) (roots : list block) : option blockset :=
  match roots with
  | [] => Some seen
  | b :: roots =>
    let* seen := visit seen b in visit_all visit seen roots
  end.

(* A depth-first acyclicity check on [region] without [cut]. [active] holds
   the current path, so a cycle is rejected immediately; [seen] memoizes
   completed blocks, so shared successors are traversed only once. Fuel
   bounds recursive depth for Rocq; the graph's block list is enough for
   any acyclic region. *)
Fixpoint visit_acyclic (fuel : list block) (region : blockset) (cut : block)
    (active seen : blockset) (b : block) : option blockset :=
  if block_eqb b cut || negb (set_mem b region) || set_mem b seen
  then Some seen
  else if set_mem b active then None
  else
    match fuel with
    | [] => None
    | _ :: fuel =>
      let* seen := visit_all
        (visit_acyclic fuel region cut (set_add b active)) seen
        (all_successors b) in
      Some (set_add b seen)
    end.

(* Check every block of the region, not just the part reached from [cut].
   The final coverage check prevents missing roots from hiding a cycle. *)
Definition acyclic_except (blocks : list block) (region : blockset)
    (cut : block) : bool :=
  match visit_all (visit_acyclic blocks region cut set_empty)
    set_empty blocks with
  | None => false
  | Some seen =>
    set_for_all (fun b => block_eqb b cut || set_mem b seen) region
  end.

(* ======================================================================== *)
(* Part 2: the intended meaning                                             *)
(* ======================================================================== *)

(* The block's instructions have no side effects and its terminator stays
   within the function. *)
Definition block_does_nothing (bl : block) : Prop :=
  (forall i, In i (block_body bl) -> has_side_effect i = false)
  /\ terminator_pure_control (terminator bl) = true.

(* [uses_only blocks same approve_instr approve_term]: in every block of
   the graph, every instruction with an argument [same] accepts satisfies
   [approve_instr], and every argument list of a terminator with a value
   [same] accepts satisfies [approve_term] with its block. *)
Definition uses_only (blocks : list block) (same : value -> bool)
    (approve_instr : instr -> Prop)
    (approve_term : block -> list value -> Prop) : Prop :=
  forall bl, In bl blocks ->
    (forall i, In i (block_body bl) ->
       existsb same (args_of_instr i) = true -> approve_instr i)
    /\ (forall arr, In arr (terminator_args (terminator bl)) ->
          existsb same arr = true -> approve_term bl arr).

(* The terminator of [bl] is a [Goto] to [target] whose argument at
   position [k] is [v], and no other argument is ([count_occurrences ... =
   one]: one position passes it). *)
Definition passes_at (target : block) (k : int) (v : value) (bl : block)
    : Prop :=
  exists args,
    terminator bl = Terminator.Continue (Goto target) args
    /\ arg_value args k = Some v
    /\ count_occurrences (arg_is v) args = one.

(* The successor relation restricted to [region] without [cut], oriented
   for accessibility: following an edge decreases in the relation. *)
Definition region_edge (region : blockset) (cut s b : block) : Prop :=
  set_mem b region = true /\ b <> cut
  /\ set_mem s region = true /\ s <> cut /\ In s (all_successors b).

(* An execution cannot stay in the region forever without visiting [cut]. *)
Definition no_infinite_path_except (region : blockset) (cut : block) : Prop :=
  forall path : nat -> block,
    (forall n, set_mem (path n) region = true /\ path n <> cut
       /\ In (path (S n)) (all_successors (path n))) -> False.

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

(* --- Block equality and sets --- *)

(* [block_eqb] is equality: it accepts a block and itself, and rejects two
   different blocks. *)
Lemma block_eqb_refl : forall b, block_eqb b b = true.
Proof. intros b. apply block_eqb_spec. reflexivity. Qed.

(* Two different blocks are told apart. *)
Lemma block_eqb_neq : forall a b, a <> b -> block_eqb a b = false.
Proof.
  intros a b H. destruct (block_eqb a b) eqn:E; [ | reflexivity ].
  apply block_eqb_spec in E. contradiction.
Qed.

(* Membership in a set after [set_add], and in a singleton. *)
Lemma set_mem_add_iff : forall b x s,
  set_mem b (set_add x s) = true <-> b = x \/ set_mem b s = true.
Proof.
  intros b x s. rewrite set_mem_add, orb_true_iff, block_eqb_spec. tauto.
Qed.

(* A singleton holds its element and nothing else. *)
Lemma set_mem_singleton_iff : forall b x,
  set_mem b (set_singleton x) = true <-> b = x.
Proof. intros b x. rewrite set_mem_singleton. apply block_eqb_spec. Qed.

(* --- Acyclic regions --- *)

Section Acyclic.
  Variable region : blockset.
  Variable cut : block.

  Definition completed (seen : blockset) : Prop :=
    forall b, set_mem b seen = true -> Acc (region_edge region cut) b.

  Definition covered (seen : blockset) (b : block) : Prop :=
    b = cut \/ set_mem b region = false \/ set_mem b seen = true.

  Definition includes (old new : blockset) : Prop :=
    forall b, set_mem b old = true -> set_mem b new = true.

  (* Growing the completed set preserves coverage of a block. *)
  Lemma covered_includes : forall old new b,
    includes old new -> covered old b -> covered new b.
  Proof.
    intros old new b Hinc [H | [H | H]];
      [ left | right; left | right; right ]; auto.
  Qed.

  (* A skipped block is outside the region, the cut, or already completed. *)
  Lemma skipped_covered : forall seen b,
    block_eqb b cut || negb (set_mem b region) || set_mem b seen = true ->
    covered seen b.
  Proof.
    intros seen b H. apply orb_true_iff in H. destruct H as [H | H].
    - apply orb_true_iff in H. destruct H as [H | H].
      + left. apply block_eqb_spec. exact H.
      + right; left. apply negb_true_iff. exact H.
    - right; right. exact H.
  Qed.

  (* Visiting a list preserves completed blocks and covers every root. *)
  Lemma visit_all_spec : forall visit,
    (forall seen b out, completed seen -> visit seen b = Some out ->
       completed out /\ includes seen out /\ covered out b) ->
    forall roots seen out,
      completed seen -> visit_all visit seen roots = Some out ->
      completed out /\ includes seen out
      /\ forall b, In b roots -> covered out b.
  Proof.
    intros visit Hvisit roots. induction roots as [|b roots IH];
      intros seen out Hseen H; cbn [visit_all] in H.
    - injection H as <-. split; [ exact Hseen | ].
      split; [ intros x Hx; exact Hx | intros x Hx; contradiction ].
    - destruct (visit seen b) as [next |] eqn:Hv; [ | discriminate ].
      destruct (Hvisit _ _ _ Hseen Hv) as [Hnext [Hinc Hcover]].
      destruct (IH _ _ Hnext H) as [Hout [Hinc' Hcovers]].
      split; [ exact Hout | ]. split.
      + intros x Hx. apply Hinc', Hinc. exact Hx.
      + intros x [<- | Hx].
        * eapply covered_includes; eassumption.
        * apply Hcovers. exact Hx.
  Qed.

  (* Successful DFS visits only complete accessible blocks: every in-region
     successor has already completed before its predecessor is added. *)
  Lemma visit_acyclic_spec : forall fuel active seen b out,
    completed seen -> visit_acyclic fuel region cut active seen b = Some out ->
    completed out /\ includes seen out /\ covered out b.
  Proof.
    induction fuel as [|x fuel IH]; intros active seen b out Hseen H;
      cbn [visit_acyclic] in H;
      destruct (block_eqb b cut || negb (set_mem b region) || set_mem b seen)
        eqn:Hskip.
    - injection H as <-. split; [ exact Hseen | ].
      split; [ intros a Ha; exact Ha | apply skipped_covered; exact Hskip ].
    - destruct (set_mem b active); discriminate.
    - injection H as <-. split; [ exact Hseen | ].
      split; [ intros a Ha; exact Ha | apply skipped_covered; exact Hskip ].
    - destruct (set_mem b active); [ discriminate | ].
      destruct (visit_all
        (visit_acyclic fuel region cut (set_add b active)) seen
        (all_successors b)) as [next |] eqn:Hnext; [ | discriminate ].
      injection H as <-.
      destruct (visit_all_spec _ (IH (set_add b active)) _ _ _ Hseen Hnext)
        as [Hdone [Hinc Hchildren]].
      split.
      + intros a Ha. apply set_mem_add_iff in Ha. destruct Ha as [-> | Ha].
        * constructor. intros s [_ [_ [Hs [Hcut Hedge]]]].
          destruct (Hchildren s Hedge) as [H | [H | H]].
          -- contradiction.
          -- rewrite Hs in H. discriminate.
          -- apply Hdone. exact H.
        * apply Hdone. exact Ha.
      + split.
        * intros a Ha. apply set_mem_add_iff. right. apply Hinc. exact Ha.
        * right; right. apply set_mem_add_iff. left. reflexivity.
  Qed.

  (* Accessibility excludes an infinite sequence of successor steps. *)
  Lemma accessible_no_path : forall b,
    Acc (region_edge region cut) b ->
    forall path : nat -> block, path 0%nat = b ->
      (forall n, region_edge region cut (path (S n)) (path n)) -> False.
  Proof.
    intros b Hacc. induction Hacc as [b Hb IH].
    intros path Hroot Hedge.
    assert (Hnext : region_edge region cut (path 1%nat) b).
    { rewrite <- Hroot. exact (Hedge 0%nat). }
    apply (IH _ Hnext (fun n => path (S n)) eq_refl).
    intro n. apply Hedge.
  Qed.
End Acyclic.

(* --- Goto arguments --- *)

(* [goto_args] reads the terminator. *)
Lemma goto_args_terminator : forall target pred args,
  goto_args target pred = Some args ->
  terminator pred = Terminator.Continue (Goto target) args.
Proof.
  intros target pred args H. unfold goto_args in H.
  destruct (terminator pred) as [ [goto | | | ] args' | | | ];
    try discriminate.
  destruct (block_eqb goto target && _) eqn:Hc; [ | discriminate ].
  injection H as <-. apply andb_true_iff in Hc. destruct Hc as [Hgoto _].
  apply block_eqb_spec in Hgoto. subst goto. reflexivity.
Qed.

(* [arg_value] reads the argument list. *)
Lemma arg_value_nth : forall args i u,
  arg_value args i = Some u -> nth_int args i = Some (Terminator.Arg u).
Proof.
  intros args i u H. unfold arg_value in H.
  destruct (nth_int args i) as [ [a | ] | ]; try discriminate.
  injection H as <-. reflexivity.
Qed.

(* --- Uses --- *)

(* [uses_only] with weaker approvals follows from [uses_only] with
   stronger ones. *)
Lemma uses_only_weaken : forall blocks same P P' Q Q',
  (forall i, P i -> P' i) -> (forall bl arr, Q bl arr -> Q' bl arr) ->
  uses_only blocks same P Q -> uses_only blocks same P' Q'.
Proof.
  intros blocks same P P' Q Q' HP HQ H bl Hbl.
  destruct (H bl Hbl) as [Hi Ht]. split.
  - intros i Hin Huse. apply HP, Hi; assumption.
  - intros arr Hin Huse. apply HQ, Ht; assumption.
Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

(* A successfully checked region has no infinite path avoiding the cut. *)
Theorem acyclic_except_sound : forall blocks region cut,
  acyclic_except blocks region cut = true ->
  no_infinite_path_except region cut.
Proof.
  intros blocks region cut H path Hpath. unfold acyclic_except in H.
  destruct (visit_all (visit_acyclic blocks region cut set_empty)
    set_empty blocks)
    as [seen |] eqn:Hv; [ | discriminate ].
  assert (Hempty : completed region cut set_empty).
  { intros b Hb. rewrite set_mem_empty in Hb. discriminate. }
  destruct (visit_all_spec region cut _
    (visit_acyclic_spec region cut blocks set_empty) _ _ _ Hempty Hv)
    as [Hdone _].
  rewrite set_for_all_spec in H.
  destruct (Hpath 0%nat) as [Hmem [Hcut _]].
  specialize (H _ Hmem). apply orb_true_iff in H. destruct H as [H | H].
  - apply block_eqb_spec in H. contradiction.
  - eapply (accessible_no_path region cut _ (Hdone _ H) path eq_refl).
    intro n. destruct (Hpath n) as [Hb [Hbc Hedge]].
    destruct (Hpath (S n)) as [Hs [Hsc _]].
    repeat split; assumption.
Qed.

(* A block [block_effect_free] accepts does nothing. *)
Theorem block_effect_free_spec : forall bl,
  block_effect_free bl = true -> block_does_nothing bl.
Proof.
  intros bl H. unfold block_effect_free in H.
  apply andb_true_iff in H. destruct H as [Hi Ht].
  split; [ | exact Ht ].
  rewrite forallb_forall in Hi. intros i Hin.
  specialize (Hi i Hin). apply negb_true_iff in Hi. exact Hi.
Qed.

(* What [all_uses_ok] checks, read back as [uses_only]: the approvals, as
   propositions, hold of every use. *)
Theorem all_uses_ok_spec : forall blocks same approve_instr approve_term,
  all_uses_ok blocks same approve_instr approve_term = true ->
  uses_only blocks same
    (fun i => approve_instr i = true)
    (fun bl arr => approve_term bl arr = true).
Proof.
  intros blocks same approve_instr approve_term H bl Hbl.
  unfold all_uses_ok in H. rewrite forallb_forall in H.
  specialize (H bl Hbl). apply andb_true_iff in H. destruct H as [Hi Ht].
  rewrite forallb_forall in Hi, Ht.
  split.
  - intros i Hin Huse. specialize (Hi i Hin).
    rewrite Huse in Hi. exact Hi.
  - intros arr Hin Huse. specialize (Ht arr Hin).
    rewrite Huse in Ht. exact Ht.
Qed.

(* What [goto_passes] checks, read back as [passes_at]. *)
Theorem goto_passes_spec : forall target k v bl,
  goto_passes target k v bl = true -> passes_at target k v bl.
Proof.
  intros target k v bl H. unfold goto_passes in H. unfold passes_at.
  destruct (terminator bl) as [ [goto | | | ] args | | | ]; try discriminate.
  apply andb_true_iff in H. destruct H as [H Hcount].
  apply andb_true_iff in H. destruct H as [Hgoto Harg].
  apply block_eqb_spec in Hgoto. subst goto.
  destruct (arg_value args k) as [a | ] eqn:Hav; [ | discriminate ].
  apply value_eqb_spec in Harg. subst a.
  apply eqb_int in Hcount.
  exists args. split; [ reflexivity | split; [ exact Hav | exact Hcount ] ].
Qed.
