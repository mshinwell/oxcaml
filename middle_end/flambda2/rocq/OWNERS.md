# Who owns which file of the Flambda 2 Rocq work

This is the ownership table of `PARALLEL-PLAN.md` (sections 6 and 7): for
each workstream, its owner and the files only that owner edits. A file
has one owner. If you need a change in a file you do not own, ask its
owner; do not make it.

How to read it and keep it current:

- A stream is owned by the agent working on it, named by the stream
  (`C0`, `V1`, ...). "Unassigned" means no agent has the stream yet; the
  orchestrator says when one does, and the integrator records it here,
  with the stream's branch.
- A pattern such as `FlambdaNormalise*` covers the files that match it
  now and later, in the directory given.
- A new file is its creator's. Add it to your own stream's section in the
  commit that creates it, unless a pattern there covers it already. Edit
  no section but your own: two streams then never change the same lines
  of this file.
- `middle_end/flambda2/rocq/status/<stream>.md` is its stream's, and
  needs no entry.
- A file that no section covers is C0's.
- C0 keeps the layout of this file; the sections are their streams'.

Paths are from the root of the repository.

## C0: core owner and integrator

Owner: C0. Phase 0 was done as C0, and what it created is C0's.

- `middle_end/flambda2/rocq/FlambdaModel.v`
- `middle_end/flambda2/rocq/FlambdaKindModel.v` (the kinds, moved out of
  `FlambdaModel.v` by the change that made the primitives data)
- `middle_end/flambda2/rocq/FlambdaValue*` (the values of the machine
  and their observations, moved out of `FlambdaSemanticsSpec.v` by the
  same change)
- `middle_end/flambda2/rocq/FlambdaSemantics*`
- the signature of `eval_prim` and the statements of the laws of
  `middle_end/flambda2/rocq/FlambdaPrimitiveSpec.v`. The file is C1's,
  and a primitive is added there without asking; a change to the
  signature or to a law is a core change
- `middle_end/flambda2/rocq/FlambdaContext*`
- `middle_end/flambda2/rocq/FlambdaWellFormed*`
- `middle_end/flambda2/rocq/FlambdaMap*` (Phase 0: finite maps and sets
  of names)
- `middle_end/flambda2/rocq/FlambdaExtract.v` (a stream asks for names
  in its list with a commit of its own: `rocq/HACKING.md`, "Adding a
  module")
- `middle_end/flambda2/rocq/OWNERS.md` (Phase 0: its layout; see above)
- `middle_end/flambda2/rocq/DECISIONS.md` (the index of the labels of
  decisions and discrepancies that the tree cites; the integrator adds
  a label's line when a merge brings the label)
- `middle_end/flambda2/rocq/status/phase0.md` (Phase 0)
- `middle_end/flambda2/tests/semantics/extracted/` (generated; only the
  integrator commits it, see `rocq/HACKING.md`)
- `middle_end/flambda2/tests/semantics/dune`,
  `middle_end/flambda2/tests/semantics/gen_rules.sh` and
  `middle_end/flambda2/tests/semantics/run/dune` (Phase 0: the rules that
  run the examples; the examples themselves are V2's)
- `rocq/Makefile` (a stream asks for lines in its lists in the same way
  as for `FlambdaExtract.v`)
- `rocq/HACKING.md`
- `rocq/review-pdf.pl`
- the integration branch

Files that exist and that the plan gives to no stream. They are C0's
until the stream in brackets, whose subject they are, has an owner; then
they are that stream's, and the integrator moves the line to its
section:

- `middle_end/flambda2/rocq/FlambdaControlFlow*` (S3, with S2 for the
  switches)
- `middle_end/flambda2/rocq/FlambdaApply*` (S4)
- `middle_end/flambda2/rocq/FlambdaStatic*` (S5)

## C1 to C5: core changes

Each is designed by its owner and applied by C0, one at a time
(`PARALLEL-PLAN.md`, section 7, "Core change requests"). The owner edits
its design note, under `middle_end/flambda2/rocq/requests/`, and the new
files it creates, and lists them here; the changes to C0's files are
made by C0. On its own branch an owner may change C0's files to try the
design out; that is the request, not the change.

- C1, primitives as data. Owner: C1, on `flambda2-rocq/C1-primitives`.
  - `middle_end/flambda2/rocq/requests/C1-primitives.md` (the request)
    and `requests/C1-int-ops.py` beside it (the generator of the
    examples that compare the integer primitives with a reference)
  - `middle_end/flambda2/rocq/FlambdaPrimitive*` (the primitives, what
    they compute and the laws they obey; adding a primitive changes
    these files and no other `.v` file; see C0's section for what of
    them is the core's)
  - the conversion of primitives and of constants in
    `middle_end/flambda2/tests/tools/flsemantics.ml`, until V3 has an
    owner
  - `middle_end/flambda2/rocq/FlambdaRange*` (what a unit whose numbers
    are in range gains; the check itself is in C0's
    `FlambdaWellFormedSpec.v`)
- C2, kinds and well-formed terms. Owner: C2, on
  `flambda2-rocq/C2-epoch` (the series) and `flambda2-rocq/C2-kinds`
  (the prototype).
  - `middle_end/flambda2/rocq/requests/C2-kinds.md` (the request)
  - `middle_end/flambda2/rocq/FlambdaWellKinded*` (the check of kinds
    and its statements)
  - `middle_end/flambda2/tests/semantics/kinds_*.fl` and their
    `.expected` files
- C3, sets of closures. Owner: C3, on `flambda2-rocq/C3-closures`.
  - `middle_end/flambda2/rocq/requests/C3-closures.md`
  - `middle_end/flambda2/rocq/FlambdaClosures*` (first facts about sets
    of closures; S4's once it is staffed)
  - `middle_end/flambda2/rocq/status/C3.md`
  - the examples `middle_end/flambda2/tests/semantics/set_*.fl`, with
    their `.expected` files
- C4, heap. Owner: unassigned.
- C5, exceptions. Owner: unassigned.

## T1 to T7: types

All in `middle_end/flambda2/types/rocq/`, library `OxCamlFlambda2Types`.

- T1, grammar and meaning. Owner: T1, on `flambda2-rocq/T1-grammar`.
  - `middle_end/flambda2/types/rocq/FlambdaTypes*` (today's naive model,
    which T1 replaces)
  - `middle_end/flambda2/types/rocq/FlambdaTypeGrammar*` (the grammar
    of types)
  - `middle_end/flambda2/types/rocq/FlambdaTypeMeaning*` (what a type
    means: `type_satisfied`; `FlambdaTypeMeaningBool*` is the meaning
    as a test)
  - `middle_end/flambda2/types/rocq/FlambdaTypeWellFormed*` (when a
    type is well formed)
  - `middle_end/flambda2/types/rocq/FlambdaTypeEqual*` (when two types
    are the same type, after `Type_grammar.equal`)
  - `middle_end/flambda2/types/rocq/FlambdaTypeAliasKinds*` (the
    aliases of a type with their kinds)
  - `middle_end/flambda2/types/rocq/FlambdaTypeRename*` (renaming the
    variables of a type, and the names that a type mentions)
  - `middle_end/flambda2/types/rocq/FlambdaTypeNominal*` (types as
    things that contain names)
  - `middle_end/flambda2/types/rocq/FlambdaTypeAccess*` (what the
    provers and reification read of a type)
- T2, typing environment. Owner: T2, on `flambda2-rocq/T2-env`.
  - `middle_end/flambda2/types/rocq/FlambdaBindingTime.v` (binding times
    and name modes, after `types/env/binding_time.ml` and
    `nominal/name_mode.ml`; written first on T3's branch, which needs it)
  - `middle_end/flambda2/types/rocq/FlambdaTypingEnv*` (the typing
    environment, after `types/env/typing_env.ml`, `typing_env_level.ml`,
    `cached_level.ml` and `typing_env_extension.ml`; what satisfies one)
- T3, aliases. Owner: T3, on `flambda2-rocq/T3-aliases`.
  - `middle_end/flambda2/types/rocq/FlambdaAliases*` (today's, which T3
    replaces; `follow_aliases` is used by the validator, so a change to
    it is agreed with V1)
  - `middle_end/flambda2/types/rocq/FlambdaEnvAliases*` (the aliases of
    the typing environment, after `types/env/aliases.ml`)
- T4, meet. Owner: unassigned.
- T5, the n-way join. Owner: T5, on `flambda2-rocq/T5-join`.
  - `middle_end/flambda2/types/rocq/FlambdaJoin*` (the n-way join of
    typing environments and of types, after `types/env/join_env.ml`,
    `types/join_levels.ml` and the join functions of
    `types/meet_and_n_way_join.ml`; what a join guarantees).
    `FlambdaJoinTypes*` are T5b's, on `flambda2-rocq/T5b-join-types`.
  - `middle_end/flambda2/types/rocq/FlambdaTypeProject.v`
    (`Type_grammar.project_variables_out`)
  - `middle_end/flambda2/rocq/requests/T5-join.md`
- T6, provers and reification. Owner: T6, on `flambda2-rocq/T6-provers`.
  - `middle_end/flambda2/rocq/requests/T6-provers.md` (the plan: the
    provers, the shape of their statements, the order)
  - `middle_end/flambda2/types/rocq/FlambdaProvers*` (the provers,
    after `types/provers.ml`; `FlambdaProversStandIn.v` is a copy of
    T4's `Expanded_type` and `expand_head`, which goes when T4's file
    is under the branch)
  - `middle_end/flambda2/types/rocq/FlambdaReify*` (reification, after
    `types/reify.ml`)
- T7, differential testing of types, and the converter between the
  compiler's types and the model's. Owner: unassigned.

## S1 to S7: simplifier rewrites

Each is a pass with its proof in a file pair of its own, which its owner
creates and lists here, and the `.fl` examples that need it. V1 wires the
pass into the validator.

- S1, primitives through types. Owner: unassigned.
- S2, switch. Owner: unassigned.
- S3, continuations. Owner: unassigned.
- S4, calls. Owner: unassigned.
- S5, lets, CSE and lifting. Owner: unassigned.
- S6, unboxing of continuation parameters. Owner: unassigned.
- S7, the reaper. Out of scope for now, unassigned.

## V1: validator

Owner: unassigned. The only stream besides C0 that edits these.

- `middle_end/flambda2/rocq/FlambdaValidate*`
- `middle_end/flambda2/rocq/FlambdaCompare*`
- `middle_end/flambda2/rocq/FlambdaNormalise*`
- `middle_end/flambda2/rocq/FlambdaUnusedStatics*`

## V2: corpus and harness

Owner: V2, on `flambda2-rocq/V2-examples`, for the corpus; the tool
stays C0's for now.

- `middle_end/flambda2/tests/tools/flsemantics.ml`
- `middle_end/flambda2/tests/semantics/*.fl` and their `.expected`
  files, but for an example that a stream adds for its own work, which
  is that stream's
- `middle_end/flambda2/tests/semantics/ocaml/` (units made from OCaml
  sources: the sources, the terms, the expected files, the script that
  makes a term and the dune rules)
- `middle_end/flambda2/rocq/FlambdaBlockLoad*` (a normalisation for the
  validator, written for the corpus: the load of a field of a block
  that is known; V1's once it is staffed)
- `middle_end/flambda2/rocq/FlambdaUnusedConts*` (another: removing a
  continuation that is not used; S3's once it is staffed)
- `middle_end/flambda2/rocq/FlambdaUnbox*` (another: unboxing a number
  that is known to be boxed, untagging one that is known to be tagged;
  S1's once it is staffed)
- `middle_end/flambda2/rocq/requests/V2-missing-constructs.md`

## V3: converter

Owner: unassigned.

- the conversion from the compiler's terms to the model's. It is in
  `middle_end/flambda2/tests/tools/flsemantics.ml`, which is V2's. It
  is moved to a file of its own when V2 and V3 both have owners, and
  not before; from then until it has moved, a change to it is agreed
  between the two. Until V3 has an owner, the part of it that converts
  primitives and constants is C1's.

## N1: nominal loose ends

Owner: N1.

- `middle_end/flambda2/rocq/FlambdaNominal*` and
  `middle_end/flambda2/rocq/FlambdaAlpha*` (C0's until the step that
  retired one bisimulation)
- `middle_end/flambda2/rocq/FlambdaCompareAlpha*`
- `middle_end/flambda2/rocq/FlambdaBinders*` (the free names of a term,
  and the checks of rows 3, 5 and 6 of well-formedness; that they are
  conjuncts of `well_formed_unit` is C0's to write)
- `middle_end/flambda2/rocq/FlambdaScope*`
- `middle_end/flambda2/rocq/FlambdaFreeNames*`
- `middle_end/flambda2/rocq/FlambdaNameAbstraction*`
- `middle_end/flambda2/rocq/FlambdaEquivariance*`
- `middle_end/flambda2/rocq/FlambdaNominalInstances*`
- `middle_end/flambda2/rocq/NAMES.md`

## N2: the freshness quantifier

Owner: N2.

- `middle_end/flambda2/rocq/FlambdaFreshQuantifier*`
- `middle_end/flambda2/rocq/FlambdaFreshAbstraction*`

## R1, R2: reviewers

Owner: R1, on `flambda2-rocq/R1-review`. R2 is unassigned. They write
no proofs.

- `ROCQ-REVIEW-GUIDE.md`
- `rocq/TRUST-LEDGER.md` (Phase 0 wrote the first version; no stream
  may add to it without a reviewer's sign-off)

## The human

- `middle_end/flambda2/rocq/PARALLEL-PLAN.md`
- the decisions listed in its section 7 ("Decisions that are a human's")
