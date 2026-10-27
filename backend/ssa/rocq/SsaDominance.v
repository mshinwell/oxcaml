(* Dominance in an SSA graph, beyond the [dominates] test SsaModel.v takes
   from the compiler: strict dominance, a sufficient condition for an edge
   to dominate a block, and what dominance means in terms of paths. The
   extraction of this file, SsaDominance.ml, is the implementation.

   See the reading guide at the top of backend/ssa/loop/rocq/
   LoopComparisons.v for the Rocq vocabulary and SsaModel.v for how the
   models see an SSA graph. As there, the file has four parts: (1) the
   definitions, (2) the intended meaning, (3) stepping-stone lemmas, (4)
   the theorems. Parts 1 and 2 are the part to check by eye.

   The result, in part 4, is [edge_dominates_sound]: the sufficient
   condition [edge_dominates] has for an edge to dominate a block is one;
   every path from the entry to the block traverses the edge.

   The trusted part is SsaModel.v: that [predecessors] lists the sources of
   the edges into a block, that [dominates d b] means every path from the
   entry to [b] passes through [d], and that the entry dominates every block
   (every block of a finished graph is reachable from it). The last two
   are [dominance_semantics] in part 2, which the theorem assumes. *)

From Stdlib Require Import Bool List.
From OxCamlSsa Require Import SsaModel SsaGraph.
Import ListNotations.

(* ======================================================================== *)
(* Part 1: the definitions                                                  *)
(* ======================================================================== *)

(* [dominator] dominates [block] and is not it. *)
Definition strictly_dominates (dominator block : block) : bool :=
  dominates dominator block && negb (block_eqb dominator block).

(* A sufficient condition for the edge [pred -> succ] to dominate [target]:
   [succ] dominates [target] and the edge is the only way into [succ]. The
   middle test excludes [succ] being the graph's entry, which has a
   predecessor when the function calls itself in tail position ([Continue
   (Goto entry)]): paths from the entry to [target] then start at [succ]
   without taking the edge. On a finished graph, where every block is
   reachable from the entry, a block that dominates its only predecessor
   can only be the entry. *)
Definition edge_dominates (pred succ target : block) : bool :=
  dominates succ target
  && negb (dominates succ pred)
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

(* ======================================================================== *)
(* Part 3: lemmas used by the proofs                                        *)
(* ======================================================================== *)

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

  (* An edge [edge_dominates] accepts for [target] is on every path from
     the entry to [target]. *)
  Theorem edge_dominates_sound : forall (pred succ target : block),
    edge_dominates pred succ target = true ->
    forall (p : list block), path entry p target -> edge_on p pred succ.
  Proof.
    intros src succ target H p Hp. unfold edge_dominates in H.
    apply andb_true_iff in H. destruct H as [H Hpred].
    apply andb_true_iff in H. destruct H as [Hd Hnd].
    destruct (predecessors succ) as [ | p0 [ | ? ? ] ] eqn:Hps;
      try discriminate.
    apply block_eqb_spec in Hpred. subst p0.
    apply (path_edge_to entry p target succ src Hp).
    - exact (dominance.(dominates_spec) succ target Hd p Hp).
    - intros ->. rewrite dominance.(entry_dominates) in Hnd. discriminate.
    - exact Hps.
  Qed.
End Dominance.
