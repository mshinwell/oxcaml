(* A Rocq model of [backend/ssa/loop/dead_induction_var.ml].

   See the reading guide at the top of LoopComparisons.v for the Rocq
   vocabulary, SsaModel.v for how the models see an SSA graph, and
   InductionVar.v and LoopTermination.v for the basic induction variables
   and the exit branches this file is given. As there, the file has four
   parts: (1) a transcription of the OCaml, (2) the intended meaning, (3)
   stepping-stone lemmas, (4) the theorems. Parts 1 and 2 are the part to
   check by eye.

   The OCaml walks the graph's blocks with an [ok] reference that any
   unapproved use clears; here [all_uses_ok] is the conjunction over the
   blocks, [count_occurrences] counts over a list, and the arrays of
   arguments are lists.

   Why the uses of the exit comparison are checked ([cond_ok]): deleting
   the loop (DeleteEmptyLoops.v) leaves the comparison computed from the
   loop's initial parameters, so a use of it other than the header's
   branch -- an instruction, or a [Return] of it after the loop -- would
   observe a value the iteration that ended the loop did not produce. The
   first version of the OCaml did not check this; the error was found
   while writing the model.

   The result, in part 4, is [analyze_spec]: for each basic induction
   variable reported dead, [dead_spec] (part 2) holds, which spells out
   what the OCaml checked of every instruction and terminator of the
   graph: the parameter is used only by the exit comparison and its own
   updates, the exit comparison only by the header's branch, and each
   update only by the exit comparison and as that parameter's argument of
   its back edge's [Goto]; and that a loop reported useless has every
   header parameter among its dead induction variables. *)

From Stdlib Require Import ZArith Lia Bool List.
From OxcamlStdlib Require Import OcamlOption OcamlInt OcamlList.
From OxcamlSsa Require Import SsaModel.
From OxcamlLoop Require Import NaturalLoop InductionVar LoopTermination.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: transcription of the OCaml                                       *)
(* ======================================================================== *)

Local Open Scope sint63_scope.

(* OCaml [biv_result] and [loop_result]. After these, the type [biv] of
   InductionVar.v is written [InductionVar.biv], its field [loop]
   [InductionVar.loop]. *)
Record biv_result : Type :=
  { biv : biv;
    dead : bool }.

Record loop_result : Type :=
  { loop : natural_loop;
    bivs : list biv_result;
    useless : bool }.

(* OCaml [instr_defines_value]. *)
Definition instr_defines_value (i : instr) (v : value) : bool :=
  match view_instr i, view_value v with
  | Op id _, Res id' _ => instr_id_eqb id id'
  | _, _ => false
  end.

(* OCaml [args_of_instr]. *)
Definition args_of_instr (i : instr) : list value :=
  match view_instr i with
  | Op _ args => args
  | Push_trap | Pop_trap => []
  end.

(* OCaml [terminator_args]. *)
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

(* OCaml [count_occurrences]. *)
Definition count_occurrences {A} (same : A -> bool) (l : list A) : int :=
  OcamlList.fold_left (fun n x => if same x then n + one else n) zero l.

(* OCaml [all_uses_ok], on the graph's block list: its [ok] reference,
   cleared by any use [same] accepts that the approval does not, is this
   conjunction. *)
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

(* OCaml [is_dead]. The OCaml's [Array.length args > k && match args.(k)
   with Arg a -> ... | Omitted_since_unused -> false] is the [match] on
   [arg_value args k] (InductionVar.v). *)
Definition is_dead (blocks : list block) (biv : InductionVar.biv) : bool :=
  match find_exit_branch biv.(InductionVar.loop) with
  | None => false
  | Some exit_info =>
    let cond := exit_info.(condition) in
    let header := biv.(InductionVar.loop).(header) in
    let k := biv.(param_index) in
    let is_self := is_header_param header k in
    let back_preds := back_edge_set biv.(InductionVar.loop) in
    (* Uses of [self]: approved only when the consumer is the exit
       comparison or one of the update expressions, never a terminator. *)
    let self_ok :=
      all_uses_ok blocks is_self
        (fun i =>
          instr_defines_value i cond
          || existsb (instr_defines_value i) biv.(update))
        (fun _ _ => false)
    in
    (* Uses of the exit comparison: approved only as the index of the
       header's [Switch]. *)
    let cond_ok :=
      all_uses_ok blocks (value_eqb cond)
        (fun _ => false)
        (fun bl _ => block_eqb bl header)
    in
    if negb (self_ok && cond_ok)
    then false
    else
      (* Uses of each update value: approved only as an argument of the
         exit comparison, or as the back-edge [Goto]'s argument at
         position [k], and at no other position of that [Goto]. *)
      forallb
        (fun v =>
          all_uses_ok blocks (value_eqb v)
            (fun i => instr_defines_value i cond)
            (fun bl _ =>
              set_mem bl back_preds
              && match terminator bl with
                 | Terminator.Continue (Goto goto) args =>
                   block_eqb goto header
                   && (match arg_value args k with
                       | Some a => value_eqb a v
                       | None => false
                       end)
                   && (count_occurrences
                         (fun arg =>
                           match arg with
                           | Terminator.Arg a => value_eqb a v
                           | Terminator.Omitted_since_unused => false
                           end)
                         args
                       =? one)
                 | Terminator.Continue (Return | Raise _ | Unreachable) _
                 | Terminator.Switch _ _ | Terminator.Call _
                 | Terminator.Invalid _ => false
                 end))
        biv.(update)
  end.

(* OCaml [loop_is_useless]. *)
Definition loop_is_useless (loop : natural_loop) (bivs : list biv_result)
    : bool :=
  same_length (params loop.(header)) bivs && forallb dead bivs.

(* OCaml [analyze], on the graph's block list. *)
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

(* What [dead = true] establishes of a basic induction variable [b] of a
   loop with the exit branch [exit_info]: its parameter [self] is used only
   by the exit comparison and its own updates and by no terminator; the
   exit comparison is used by no instruction and only by the header's
   terminator; and each update value is used by no instruction but the
   exit comparison, and by no terminator but the [Goto] to the header of
   a back-edge block, as the argument at the parameter's position and at
   no other ([count_occurrences ... = one]: one position passes it). *)
Definition dead_spec (blocks : list block) (b : InductionVar.biv) : Prop :=
  exists exit_info,
    find_exit_branch b.(InductionVar.loop) = Some exit_info
    /\ let cond := exit_info.(condition) in
       let header := b.(InductionVar.loop).(header) in
       let k := b.(param_index) in
       uses_only blocks (is_header_param header k)
         (fun i =>
           instr_defines_value i cond = true
           \/ exists u, In u b.(update) /\ instr_defines_value i u = true)
         (fun _ _ => False)
       /\ uses_only blocks (value_eqb cond)
            (fun _ => False)
            (fun bl _ => bl = header)
       /\ forall u, In u b.(update) ->
            uses_only blocks (value_eqb u)
              (fun i => instr_defines_value i cond = true)
              (fun bl _ =>
                In bl b.(InductionVar.loop).(back_edges)
                /\ exists args,
                     terminator bl = Terminator.Continue (Goto header) args
                     /\ arg_value args k = Some u
                     /\ count_occurrences
                          (fun arg =>
                            match arg with
                            | Terminator.Arg a => value_eqb a u
                            | Terminator.Omitted_since_unused => false
                            end)
                          args
                        = one).

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

Lemma all_uses_ok_spec : forall blocks same approve_instr approve_term,
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

Lemma uses_only_weaken : forall blocks same P P' Q Q',
  (forall i, P i -> P' i) -> (forall bl arr, Q bl arr -> Q' bl arr) ->
  uses_only blocks same P Q -> uses_only blocks same P' Q'.
Proof.
  intros blocks same P P' Q Q' HP HQ H bl Hbl.
  destruct (H bl Hbl) as [Hi Ht]. split.
  - intros i Hin Huse. apply HP, Hi; assumption.
  - intros arr Hin Huse. apply HQ, Ht; assumption.
Qed.

(* The approval of a terminator use of an update value, read back. *)
Lemma update_term_approved : forall b header k v bl,
  set_mem bl (back_edge_set b.(InductionVar.loop))
  && match terminator bl with
     | Terminator.Continue (Goto goto) args =>
       block_eqb goto header
       && (match arg_value args k with
           | Some a => value_eqb a v
           | None => false
           end)
       && (count_occurrences
             (fun arg =>
               match arg with
               | Terminator.Arg a => value_eqb a v
               | Terminator.Omitted_since_unused => false
               end)
             args
           =? one)
     | Terminator.Continue (Return | Raise _ | Unreachable) _
     | Terminator.Switch _ _ | Terminator.Call _ | Terminator.Invalid _ =>
       false
     end = true ->
  In bl b.(InductionVar.loop).(back_edges)
  /\ exists args,
       terminator bl = Terminator.Continue (Goto header) args
       /\ arg_value args k = Some v
       /\ count_occurrences
            (fun arg =>
              match arg with
              | Terminator.Arg a => value_eqb a v
              | Terminator.Omitted_since_unused => false
              end)
            args
          = one.
Proof.
  intros b header k v bl H. apply andb_true_iff in H. destruct H as [Hset H].
  apply back_edge_set_spec in Hset. split; [ exact Hset | ].
  destruct (terminator bl) as [ [goto | | | ] args | | | ]; try discriminate.
  apply andb_true_iff in H. destruct H as [H Hcount].
  apply andb_true_iff in H. destruct H as [Hgoto Harg].
  apply block_eqb_spec in Hgoto. subst goto.
  destruct (arg_value args k) as [a | ] eqn:Hav; [ | discriminate ].
  apply value_eqb_spec in Harg. subst a.
  apply eqb_int in Hcount.
  exists args. split; [ reflexivity | split; [ exact Hav | exact Hcount ] ].
Qed.

(* ======================================================================== *)
(* Part 4: theorems                                                         *)
(* ======================================================================== *)

Theorem is_dead_spec : forall blocks b,
  is_dead blocks b = true -> dead_spec blocks b.
Proof.
  intros blocks b H. unfold is_dead in H.
  destruct (find_exit_branch b.(InductionVar.loop)) as [exit_info | ]
    eqn:Hexit; [ | discriminate ].
  cbv zeta in H.
  destruct (negb (_ && _)) eqn:Hok; [ discriminate | ].
  apply negb_false_iff, andb_true_iff in Hok. destruct Hok as [Hself Hcond].
  rewrite forallb_forall in H.
  exists exit_info. split; [ exact Hexit | ]. cbv zeta.
  split; [ | split ].
  - apply all_uses_ok_spec in Hself.
    refine (uses_only_weaken _ _ _ _ _ _ _ _ Hself).
    + intros i Hi. apply orb_true_iff in Hi. destruct Hi as [Hi | Hi].
      * left. exact Hi.
      * right. apply existsb_exists in Hi. exact Hi.
    + intros bl arr Hf. discriminate.
  - apply all_uses_ok_spec in Hcond.
    refine (uses_only_weaken _ _ _ _ _ _ _ _ Hcond).
    + intros i Hi. discriminate.
    + intros bl arr Hbl. apply block_eqb_spec. exact Hbl.
  - intros u Hu. specialize (H u Hu). apply all_uses_ok_spec in H.
    refine (uses_only_weaken _ _ _ _ _ _ _ _ H).
    + intros i Hi. exact Hi.
    + intros bl arr Hbl. apply update_term_approved. exact Hbl.
Qed.

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
