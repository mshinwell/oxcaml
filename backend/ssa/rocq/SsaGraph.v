(* Properties of the blocks, terminators, instructions and values of an SSA
   graph that any pass may ask about, computed on the views of SsaModel.v:
   what a terminator does, what an instruction or a terminator reads, which
   values a block's [Goto] passes, and whether every use of a value in the
   graph is an approved one. The extraction of this file, SsaGraph.ml, is
   the implementation.

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
  match view_instr i, view_value v with
  | Op id _, Res id' _ => instr_id_eqb id id'
  | _, _ => false
  end.

(* The values an instruction reads. *)
Definition args_of_instr (i : instr) : list value :=
  match view_instr i with
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
