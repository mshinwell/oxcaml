# Matching the loop models on the compiler's values

Date: 2026-10-27. An assessment of commit d978dee77a, which removed the
translation between the compiler's SSA structures and the Rocq models
under `backend/ssa/rocq/` and `backend/ssa/loop/rocq/`.

## The two designs

Before, `SsaModel.v` declared values, instructions and terminators as
abstract types, and the models observed them through `Parameter`s such
as `view_value`, realised by `backend/ssa/ssa_view.ml`. That module
rebuilt each piece of compiler data as a term of the model and, for the
linearizer of `AffineSsa.v`, unfolded a value's defining instructions
into a tree of at most 256 nodes, which the model then walked.

Now the model's `value`, `instr` and `Terminator.t` are `Inductive`
types copying the compiler's, with the fields the models read, and
`Extract Inductive` maps each back onto the compiler's type through a
match function. The models match on `Ssa.Value.t` itself. The
linearizer walks the value graph directly, under a budget of nodes
carried in its context.

## What improved

- **The trusted base shrank.** `ssa_view.ml` was about 130 lines of
  unverified OCaml, and its tree builder carried the 256-node bound as
  a documented property. What replaces it is four match functions of a
  few lines each in `SsaModelExtract.v`, each of which only destructures
  a record and converts an array to a list. The node bound is now a Rocq
  definition with a proof, and the axiom `tree_of_value_root` is gone.
- **One representation instead of two.** The model's `value` is the
  compiler's value, so there is no tree type, no root field, no fuel,
  and no question of whether the translation was faithful. A new
  recognised operation needs edits in `expr_of_value` and
  `op_semantics` only.
- **Simpler hypotheses.** `machine_values.iter_op` says just
  `op_semantics (iter n) v`, and `atom_counter_fits` no longer
  quantifies over values: it is the constant `linearize_atoms` plus the
  size of the header's guards. Finding 1 of `ROCQ-VACUITY-AUDIT.md` is
  now one lemma away from a statement through primitives only: bound
  `guards_size` by `cond_atoms` times the length of `strict_dominators`.
- **Drift is caught by the compiler.** If a field or constructor in
  `backend/ssa/ssa.mli` changes, the match strings stop compiling. The
  old view module could drift in meaning while still compiling.

## What it costs

- **A less common extraction feature.** `Extract Inductive` with a
  match function is seen less often than `Extract Constant`, and every
  `match` on a value in the extracted code becomes the application of a
  closure rather than a native `match`. The extracted `AffineSsa.ml`
  reads worse at those sites.
- **An allocation per match.** Each match converts the argument array
  to a list. With a 256-node budget this is negligible, but the old
  design converted once per tree.
- **A slightly stronger reading of `value_eqb_spec`.** Equality of Rocq
  terms now means equality of id, operation, arguments and index. That
  matches identity of the compiler's value only because instruction ids
  are unique in a graph, which the comment in `SsaModel.v` states but
  nothing checks. The `Inductive` also takes for granted that a value is
  a finite term, with no cycle through `Res` arguments, which SSA
  guarantees because an instruction's arguments are defined before it.
- **Two warts.** The empty `module Terminator = struct end` in the
  extracted `SsaModel.ml`, since the Rocq module's one type is mapped
  onto the compiler's; and the nested-inductive induction principle
  `value_ind'` that the proofs need because the generated one is too
  weak.

## Verdict

None of the costs concern soundness. The first design put the
correctness of the glue on a reader of OCaml; this one puts it on four
structural match functions and on Rocq. The second design is the one to
keep.
