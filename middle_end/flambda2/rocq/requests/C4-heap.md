# C4, the heap: core change request

Stream C4 of `PARALLEL-PLAN.md` (section 6). This is the request of
section 7 ("Core change requests"), and it is a design for a human to
decide on before anything is applied: how the heap is modelled and what
is observable are the human's (plan, section 7).

**This is the third version.** R2 reviewed the second, with its
prototype, and required changes; its five blocking findings and its corrections of text are answered here,
and "What changed since the second version", after the summary, says
where. Two things changed that R2 did not ask for: the relation at
exit was found not to be transitive, for a reason other than R2's, and
is redefined (section 3.2), with transitivity now proved; and the
front end has been read for decision 4, which the human has ruled on
in part.

Paths are in `middle_end/flambda2/` unless they say otherwise. The base
is the integration branch at 66bbc6b1be: C1's epoch, with its law that
no primitive has a value on a symbol bound to nothing, and its numbers
in range; C3's epoch, sets of closures of several functions, and valid
values; C2's epoch, in which terms carry kinds and arities and a call
is undefined unless it agrees with the code called; C5's epoch, in
which a call gives extra arguments to its exception continuation and
an `Apply_cont` has a trap action; C0's well-formedness; N1's names;
and the types, T1's to T6's. It is read together with C0's note on
well-formedness (`requests/C0-well-formed.md`). The prototype was
written on 0a2933e7c9 and has been rebased on 66bbc6b1be; what that
cost each owner, and what changed in the prototype, is in
`requests/C4-heap-fallout.md`.

The prototype is on the branch `flambda2-rocq/C4-heap`. It builds
(`make -C rocq -j16 all`, `make -C rocq assumptions`), and has no
`Admitted`, axiom or `Parameter`. It is in two parts:

- edits to four existing files, to measure what a new form of value
  and new primitives cost: `FlambdaValueSpec.v` (locations, cells, the
  heap, `Value_location`), `FlambdaPrimitiveModel.v` and
  `FlambdaPrimitiveSpec.v` (the primitives of the heap), and the
  repairs they need;
- two new files, `FlambdaHeapSpec.v` and `FlambdaHeapProofs.v`: a
  machine with a heap beside the one that exists, what the primitives
  do, the classification by effects and coeffects with its laws, the
  relation at exit, the relation on states that the machine
  respects, and the statements Simplify needs. Thirty-six statements
  are proved, and none is left as a conjecture.

It does not put the heap in the state of `FlambdaSemanticsSpec.v`:
section 7 says what that sweep is and why I counted it and did not
finish it. Section 10 says what the prototype proves and leaves.

## Summary

- **Scope.** Mutable blocks of values and `Immutable_unique` blocks,
  made at run time, with `Make_block`, `Block_load`, `Block_set`,
  `Get_tag`, `Is_int`, `Is_null` and `Phys_equal` on them. Out of the
  first version: arrays, bytes, strings that change, bigarrays, atomics,
  lazy blocks, `Duplicate_block`, `Duplicate_array`, `Obj_dup`, float
  and mixed blocks, static blocks that are not `Immutable`. **Local
  allocation is not modelled**: no lifetime, no region, no mode on an
  allocation or on an assignment. That is the model. The conversion,
  since the decision taken overnight on D37, does not refuse them: it
  drops `Begin_region`, `End_region` and `End_region_ghost` and reads
  a local allocation as one on the heap, with CRs, on the type
  checker's guarantee that nothing allocated in a region is used
  after the region ends. This is an interim scope of the conversion,
  not a design for regions (section 1.5). The conversion refuses the
  rest of the list.
- **The store.** A state gains a heap: a finite map from *locations* to
  *cells*. A location is a name (compared by equality only), chosen
  fresh at allocation by a function, so `step` stays a function. Only
  what has an identity in the compiler is a cell: blocks made `Mutable`
  or `Immutable_unique`. Immutable blocks, boxed numbers and closures
  stay values with no identity, as they are today: the compiler shares
  and duplicates them at will, and Simplify's CSE, lifting and unboxing
  do change which allocation a program sees.
- **Primitives.** `eval_prim` stays as it is for the primitives that do
  not touch the heap, with its laws. A function `exec_prim` over it
  takes and returns a heap. The compiler's classification of each
  primitive (effects, coeffects) is transcribed, and tied to
  `exec_prim` by four laws, proved in the prototype: that is what
  Simplify's licence to delete and move a `Let` rests on.
- **Exit.** An exit carries the values, the static environment and the
  heap. Two exits are compared up to a *correspondence*: a partial
  bijection between the locations of the two runs, and a bisimulation
  between their values, under which the values at exit, and every cell
  reached, agree; immutable values are compared by their contents,
  looking through symbols (this is D6); optionally a poison of the
  source may be any value of its kind in the target, inside a boxed
  number too (D26). `refines` and `equivalent` are restated with it.
  The relation is defined in the prototype and proved there to be
  reflexive on closed memories and transitive, with and without
  poison, and to say what is meant on the cases checked (it sees
  aliasing and not names; a block is a symbol bound to an equal block;
  garbage is not seen; a boxed poison is refined by a boxed number,
  whichever of the two is a symbol). The lemma on which the change
  rests is proved there too, for the relation without poison: the
  machine takes related states to related states
  (`machine_respects_relation`). From it, refinement is reflexive on
  closed states, a step keeps a state closed, and the rewrites that
  were stated are proved: deleting a binding that is not used, an
  allocation included; exchanging two bindings; sharing two
  applications of a primitive; a load from a block that is known;
  lifting a block or a closure to a symbol. Lifting needed the
  relation on states to let the second state bind symbols that the
  first neither binds nor names (`states_related_except`, section
  4.2).
- **Staging.** `Phys_equal` on immediates lands now, as a pure
  primitive in the primitives' files (integer `=` and `<>` reach
  Flambda 2 as `Phys_equal`, so no source program with an integer
  equality can be checked without it); P1 is doing it. Then three
  epochs: the heap in the state and the memory in `Exit`, with nothing
  using them (a sweep of 188 applications of `State`, mechanical);
  then cells and the primitives, exits compared as they are, which is
  strict and sound and is leaf work; then the correspondence, which is
  the one with real proof in it and is done on a branch first.
- Three places where the model makes undefined something that the
  compiled program computes, each a decision below with the CR it
  carries: `Phys_equal` of two immutable allocated values; a load
  marked `Immutable` from a block made `Mutable`; a `Block_set` into a
  block that was not made `Mutable`. Each is weaker coverage, not a
  faithful account: nothing is proved of a program that does one of
  them. The second is the weak point of the first stage: it leaves
  every record with both mutable and immutable fields undefined once
  an immutable field is read. Decision 4 is restated. What Simplify
  assumes is that a field does not change *after* it has been read as
  immutable; a second stage that enforces exactly that covers such
  records with no change to the compiler. The blocks that
  tail-modulo-cons builds, and the copy of a large record by
  `Duplicate_block`, are outside the design by the human's rulings.

## What changed since the second version

R2's review of the second version is in its review log. Its blocking
findings:

- **B1: the relation with poison was not transitive** (an inline boxed
  poison, a symbol bound to a boxed poison, a symbol bound to a boxed
  number). The contents of boxed numbers are now related in one way in
  both presentations (`contents_related`), and
  `outcome_related_transitive` is proved for both relations.
  `boxed_poison_refined` is R2's example, proved with the symbol on
  either side. Section 3.2.
- **B2: `unused_let_statement`** erases any unused named expression and
  is false of a `Block_set`. It is listed as a statement that changes
  (sections 4.2 and 8.2), and the claim that no existing statement is
  falsified is withdrawn. N1, whose file it is in, is told.
- **B3: decision 4(b) excluded initialisation followed by immutable
  reads.** Decision 4 is restated (sections 1.4 and 8.4, and the
  decision): the option that remembers history now makes undefined
  only a write *after* an immutable read, which is all that Simplify
  assumes, so a block that is filled and then read is covered. The
  human has ruled that tail-modulo-cons is outside the design. The
  front end has been read for every other store into a field that is
  later read as immutable. There is one, the copy of a large record
  for `{ r with ... }`; X5 has since shown that it is miscompiled
  (C4-4), and the human has ruled it out of the model as well. X5
  read the compilation of recursive values and found nothing. X5
  found recursive modules, which are patched after they may have been
  read, and miscompiled (X5-2); they are named as outside what
  decision 4 covers.
- **B4: names bound to nothing.** `exec_prim` has no value when an
  argument is a symbol or a location that is bound to nothing, for
  every primitive; `exec_prim_symbols_bound` and
  `exec_prim_locations_bound` are proved. Section 2.5.
- **B5: equality by contents is not preserved by Simplify.** Option
  (d) of section 2.6 is corrected, and so is the claim that option (b)
  gives a meaning wherever Simplify decides an equality.

Its corrections of text: `Bigarray_get_alignment` has no coeffects
(1.3); `Array_load` marked immutable is eligible for CSE (1.2); lifting
asks for normal name mode and for `try_to_reify` to succeed (1.2); the
law of no coeffects licenses running later and sharing, not running
before a branch (4.1); the link with N1's orbit relation is on what
the exit values reach (2.2, 3.2, 5); a type's denotation takes the
heap (2.1, 4.2); the conjecture on lifting is a refinement (3.5); what
`prove_physical_equality` answers on closures and on symbols (1.4,
2.1); the count of 69 (7.1).

From V2: where `Phys_equal` on immediates lands (2.6, 8.3).

Not asked for:

- The relation of the second version was not transitive without
  poison either, through cyclic static data. It is redefined: the
  correspondence relates values, not symbols, and is a bisimulation.
  Section 3.2 has the counterexample and the new definition.
- `simplify/unboxing/` and the front end (`lambda/`, `from_lambda/`)
  are read, for decisions 4 and 5 (section 1.4).
- The lemma on related states is proved in the prototype (section
  3.3), and with it `heap_step_closed`, `delete_unused_let`,
  `exchange_lets`, `cse_adjacent` and `load_known_field` (sections
  4.2 and 6). They were conjectures in the second version.
- Since the third version went to R2:
  - `lift_block`, `lift_closure` and `lift_closure_of_set` are
    proved, with a relation on states up to symbols that the second
    state binds (section 4.2, "Lifting").
  - The rule of the relation for closures is rewritten for C3's sets
    of closures (section 3.2, rule 3): the closures at the other
    function slots of two related closures are related
    (`related_projections`), and a closure made by a `Let` is related
    to a symbol of a static set that is bound in full. A first form
    of the rule, made in the rebase, compared the other slots by
    whether they were symbols; it related closures whose other slots
    a term could tell apart, and did not relate a closure to its
    lifted symbol. R2 and V3 both asked for the rule as it is now.
  - The relation without poison is symmetric
    (`outcome_equivalent_symmetric`).

## 1. What the compiler has

Read: `terms/flambda_primitive.ml` and `.mli`, `terms/effects.mli`,
`coeffects.mli`, `placement.mli`, `validity.mli`,
`effects_and_coeffects.ml`, `mutability.mli`, `static_const.mli`;
`simplify/simplify_let_expr.ml`, `simplify_named.ml`,
`simplify_primitive.ml`, the heap cases of
`simplify_unary_primitive.ml`, `simplify_binary_primitive.ml` and
`simplify_variadic_primitive.ml`, `simplify/lifting/reification.ml`;
`types/provers.ml` (`prove_physical_equality`, `prove_is_int`,
`prove_get_tag`, `prove_unique_tag_and_size`), the `Mutable_block`
cases of `types/meet_and_join.ml`, `types/reify.ml`;
`simplify/unboxing/`; in the front end, `lambda/lambda.mli`,
`translcore.ml`, `matching.ml`, `translprim.ml`, `translclass.ml`,
`translmod.ml`, `tmc.ml`, `value_rec_compiler.ml`, and
`from_lambda/lambda_to_flambda_primitives.ml` for what they become.

### 1.1 The classification

`Flambda_primitive.effects_and_coeffects` gives each primitive four
things (`Effects_and_coeffects.t`). The task statement names three; the
fourth, `Validity.t`, is recent.

- **Effects** (`effects.mli`): `No_effects` ("does not change the
  observable state of the world ... applications whose results are not
  used may be eliminated ... may be duplicated");
  `Only_generative_effects of Mutability.t` (an allocation and nothing
  else: may be eliminated when unused, never duplicated; the argument
  says whether what is returned is mutable); `Arbitrary_effects`.
  Running out of memory, finalisers and signal handlers are "effects
  out of the ether" and are ignored.
- **Coeffects** (`coeffects.mli`): `No_coeffects` ("does not observe
  the effects of other expressions ... must not read from any mutable
  storage"; with no effects either, "may be reordered with respect to
  other expressions, subject to data dependencies"); `Has_coeffects`.
- **Placement** (`placement.mli`): `Delay` (place as late as possible,
  even if duplicated) or `Strict`. Read by `to_cmm/` only.
- **Validity** (`validity.mli`): `Can_move_anywhere`,
  `Can't_move_before_any_branch`, `Control_flow_point`: whether a
  primitive may be moved before a branch that makes it meaningful (a
  bounds check, a match on a GADT). Every primitive is
  `Can't_move_before_any_branch`. Read by `to_cmm/` only.

`Mutability.t` has three values, and the third matters here:
`Mutable`; `Immutable` ("not only contents will never vary, but we're
also allowed to share or duplicate identical values at will");
`Immutable_unique` ("contents will never vary, but physical equality is
meaningful so the value must not be duplicated, nor shared"). The
front end makes `Immutable_unique` blocks for extension constructors,
so exceptions (C5) need them.

### 1.2 Where Simplify reads the classification

Four places, all found by `grep`; `to_cmm/` and the reaper are not
counted.

1. **Deleting a binding** (`simplify_let_expr.ml`,
   `must_be_kept_for_its_effects`). A `Let` whose variable is not used
   is deleted when its defining expression has
   `at_most_generative_effects` (`No_effects` or
   `Only_generative_effects`). Coeffects are not looked at, and nor is
   whether the primitive has a value: an unused load of something that
   is not a block is deleted. A `Simple`, a set of closures and a
   static constant always qualify.
2. **Lifting to a symbol** (`simplify_named.ml`, `allow_lifting`): only
   a primitive with `only_generative_effects` whose variable is bound
   at normal name mode, and then only if `Reification.try_to_reify`
   can rebuild its value from its type. `Mutable` blocks have
   the type `Mutable_block`, which `Reify` does not rebuild; immutable
   blocks, `Immutable_unique` ones included, and boxed numbers are
   lifted, and those that `Static_const.can_share` accepts are shared
   with an equal constant lifted before (`Immutable_unique` and
   `Mutable` blocks are never shared).
3. **CSE** (`Flambda_primitive.Eligible_for_cse.create`): a primitive
   that its own table lists as eligible, with a variable among its
   arguments, and (checked with a fatal error) `No_effects,
   No_coeffects`, or `Only_generative_effects Immutable, No_coeffects`:
   "Allow constructions of immutable blocks to be shared". So two
   `Make_block ... Immutable` of the same arguments become one
   allocation, and so do two `Box_number`. `Block_load` is not
   eligible (its information goes through the types); `Array_load`
   marked `Immutable` or `Immutable_unique` is, and so is
   `Phys_equal`.
4. **The flow analysis** (`simplify/flow/flow_acc.ml`), for which
   names are needed: the same test as 1.

Simplify does not move a `Let`. Moving is `to_cmm`'s (`Delay`, and
substitution of a pure binding at its use), which is not modelled. So
"moving a binding past another" is a statement the model can make and
that later streams may use for CSE and for unboxing, but no pass of
Simplify that the plan covers needs it today.

### 1.3 The primitives that allocate, read or write

E is effects (`No`, `Gen m` for `Only_generative_effects m`, `Arb`), C
coeffects (`No`, `Has`). Placement is `Strict` unless said. "v1" is the
first version of the heap; "later" is leaf work once the store exists,
in the order the corpus asks; "out" needs a design of its own.

| Primitive | E | C | In |
|---|---|---|---|
| `Make_block (kind, mut, mode)` | `Gen mut` | `No` (heap), `Has` (local) | v1: `Values`, heap, all three `mut` |
| `Make_array (kind, mut, mode)` | `Gen mut` | as above | later |
| `Block_load {kind; mut; field}` | `No` | `No` if `mut` is `Immutable` or `Immutable_unique`, else `Has` | v1: `Values` |
| `Block_set {kind; init; field}` | `Arb` | `No` | v1: `Values` |
| `Array_load (_, _, mut)` | `No` | by `mut`, as `Block_load` | later |
| `Array_set` | `Arb` | `No` | later |
| `Array_length` | `No` | `No` | later |
| `Duplicate_block` | `Gen Mutable` | `Has` | out, by ruling (decision 4) |
| `Duplicate_array` | `Gen dst` | `No` if the source is immutable, else `Has` | later |
| `Obj_dup` | `Gen Mutable` | `Has` | later |
| `Box_number (_, mode)` | `Gen Immutable` | `No` (heap) | have it (C1): a value, no cell. `Delay` in classic mode |
| `Unbox_number`, `Tag_immediate`, `Untag_immediate` | `No` | `No` | have them |
| a set of closures (a `named`, not a primitive) | at most generative | | have it (C3): a value, no cell |
| `Project_function_slot`, `Project_value_slot` | `No` | `No` | have them (`Delay`) |
| `Is_int`, `Is_null`, `Get_tag` | `No` | `No` | v1: on a location too |
| `Phys_equal` | `No` | `No` | v1 (decision 3) |
| `Opaque_identity` | `Arb` | `Has` | have it; never deleted |
| `String_length` | `No` | `No` | later |
| `String_or_bigstring_load` | `No` | `No` for `String`, `Has` for `Bytes` and `Bigstring` | later (strings), out (the rest) |
| `Bytes_or_bigstring_set` | `Arb` | `No` | out |
| `Bigarray_load`, `Bigarray_set`, `Bigarray_length` | reads `No`, writes `Arb` | reads `Has` | out |
| `Bigarray_get_alignment` | `No` | `No` | out |
| `Atomic_load`, `Atomic_set`, `Atomic_exchange`, `Atomic_compare_and_set`, `Atomic_compare_exchange`, `Atomic_int_arith` | `Arb` | `Has` | out (no concurrency in the model) |
| `Make_lazy` | `Gen Mutable` | `No` | out |
| `Get_header`, `Is_boxed_float`, `Is_flat_float_array` | `No` | `No` | out |
| `Peek`, `Poke`, `Read_offset`, `Write_offset`, `Int_as_pointer` | various | various | out |
| `Begin_region`, `Begin_try_region` | `Gen Mutable` | `Has` | out: local allocation |
| `End_region`, `End_try_region` | `Arb` | `Has` | out: local allocation |
| `Dls_get`, `Tls_get`, `Domain_index`, `Poll`, `Cpu_relax`, `Probe_is_enabled` | various | `Has` | out |

Two remarks on the table.

- A write has `Arbitrary_effects` and *no* coeffects, and a mutable
  load has no effects and `Has_coeffects`. So "effects" is "may change
  what a later read sees" and "coeffects" is "may see what an earlier
  write did". The laws of section 4 say exactly that of `exec_prim`.
- `Block_load` takes its coeffects from the `mut` written on the load,
  not from the block. The front end writes `Immutable` on the load of
  an immutable field of a record that also has mutable fields, and such
  a record is made with `Make_block ... Mutable`. Section 1.4 (with
  the list of what the front end makes) and decision 4 are about this.

### 1.4 What Simplify and the types say of mutable things

- `Make_block ... Mutable` has the type `Mutable_block`, which says the
  allocation mode and nothing else: not the tag, not the size, no
  field. `Immutable` and `Immutable_unique` give a `Variant` type with
  the tag and the types of the fields, and `is_unique` set for the
  second (`simplify_variadic_primitive.ml`).
- A load marked `Mutable` learns nothing; its result has the unknown
  type. It is `Invalid` only when its argument is a constant
  (`simplify_mutable_block_load`). `Block_set` is left as it is and
  teaches nothing (`simplify_block_set`).
- A load marked `Immutable` or `Immutable_unique` meets the type of its
  argument with "an immutable block of at least `field + 1` fields
  whose field `field` is the result" (`simplify_immutable_block_load0`).
  So after `x = r.a`, read as immutable, the type of `r` is a `Variant`
  that knows field `a`, and a second such load is replaced by `x`. This
  happens whether or not `r` is, at run time, a block with mutable
  fields. If the type of `r` is already `Mutable_block`, the meet keeps
  `Mutable_block` and drops the fact; the comment there
  (`meet_and_join.ml`, "This is not nice. We're more or less treating
  `Mutable_block` as more precise than `Variant`") gives the record
  `{ a : int; mutable b : int }` as the example.
  What this assumes, exactly: **once a field has been loaded as
  immutable, it does not change**. The fact is learnt at the load and
  used after it, in what the load dominates, which inlining widens
  (after `f r; g r; f r` is inlined, what the first `f` learnt of `r`
  is used in the second, across `g`). Nothing is assumed of the field
  before the load: a store before the first immutable load is harmless
  to Simplify, and Simplify moves no load of a mutable block earlier
  (see unboxing, below). Nothing in Flambda 2 checks the assumption.
  Discrepancies C4-2 and R2-20.
- The provers on `Mutable_block`: `Is_int` is proved false; `Get_tag`
  is unknown; nothing can be reified or unboxed.
- `prove_physical_equality` (`types/provers.ml`), which is all that
  `simplify_phys_equal` uses. *Proved true*: the two arguments have the
  same canonical alias (the same variable or the same symbol, whatever
  it holds, a closure included), or are the same constant, or both are
  null. *Proved false*: **two different symbols**, whatever they are
  bound to (so two static blocks with equal contents are proved
  different; R2-21 has the term); a symbol against a constant; one is
  an immediate and the other allocated; two blocks whose tags, sizes
  or shapes differ; two boxed numbers or two strings whose possible
  contents are disjoint; values of different sorts (a boxed number
  against a closure, and so on). *Unknown* otherwise; in particular
  "it would be dangerous to assume that variants, mutable blocks and
  arrays cannot alias to each other".
  Since CSE makes two equal immutable `Make_block`s aliases, a
  `Phys_equal` of them is then proved true, where the machine before
  CSE answers false. The comment on `simplify_phys_equal` says "the
  compiler defines physical equality as referential equality on all
  values, including immediates and immutable blocks", which CSE and
  the sharing of lifted constants do not keep. Discrepancy C4-3.
- Lifting does not ask where the `Let` is. An `Immutable_unique` block
  whose fields are constants or symbols is lifted to one symbol from
  inside a function, which makes one block of what was one for each
  call. The front end never makes such a block (an extension
  constructor holds a fresh id, which is a variable), so no source
  program shows it. Discrepancy C4-1, with the test that would.

**What the front end makes.** Read for decisions 4 and 5; line numbers
are those of the base.

- *Loads.* `Pfield (i, _, sem)` becomes a `Block_load` marked
  `Immutable` for `Reads_agree` and `Mutable` for `Reads_vary`
  (`lambda_to_flambda_primitives.ml:609-610`). The front end chooses by
  the field: `if Types.is_mutable lbl.lbl_mut then Reads_vary else
  Reads_agree` (`translcore.ml:897` for `r.f`, `:2644` for the fields
  kept by `{ r with ... }`; `matching.ml:2593` for a record pattern).
  Tuples, constructors and modules are read with `Reads_agree`;
  objects, classes, lazy values and `%field0`, `%field1` with
  `Reads_vary` (`translclass.ml:268, 398, 592, 1166`;
  `translcore.ml:1267, 1285`; `matching.ml:2374, 2432`;
  `translprim.ml:755-757`). A uniqueness barrier turns `Reads_agree`
  into `Reads_vary` (`lambda.ml:1171-1177`).
- *Allocations.* A record, inline records included, is made `Mutable`
  if any of its fields is mutable, and `Immutable` otherwise
  (`translcore.ml:2712-2715`). So **a load marked `Immutable` from a
  block made `Mutable` is, in ordinary code, the read of an immutable
  field of a record that also has a mutable field**: `Hashtbl.t` and
  its `seed`, for one.
- *Stores.* These are all the stores of `lambda/`:
  1. `r.f <- e` (`translcore.ml:1050-1089`): `Assignment`. The field is
     mutable by typing, and is read with `Reads_vary`.
  2. Objects and classes (`translcore.ml:2541`;
     `translclass.ml:279, 1180, 1355`): `Assignment`; read with
     `Reads_vary`.
  3. `%setfield0`, `%setfield1` (`translprim.ml:737-766`): `:=` on a
     `ref`, and whatever unsafe code does with them. `Assignment`.
  4. **The copy of a large record** (`translcore.ml:2553-2625`):
     `{ r with f = e }` on a heap record of at least
     `Config.max_young_wosize` fields is `Pduprecord`, then one
     `Psetfield ... (Assignment modify_heap)` for each field given
     (`:2579-2605`). A field given may be immutable, and is then read
     with `Reads_agree`. **It is miscompiled today**: X5's program,
     from OCaml source with the default flags, reads the old value
     from the copy (`record_update.ml`, with X5's series).
     `simplify_duplicate_block` gives the copy the type of the
     original, the stores change no type, and an immutable load from
     the copy is answered from that type. C4-4.
  5. **Tail-modulo-cons** (`tmc.ml:80, 156-168`): the constructor is
     allocated `Mutable` whatever its flag, with a placeholder in one
     field, which a later `Psetfield_computed (Pointer,
     Heap_initialization)` fills; to its readers the block is then an
     ordinary immutable constructor, read with `Reads_agree`. This is
     the only producer of `Heap_initialization`, and
     `Root_initialization` is a fatal error on entry to Flambda 2
     (`lambda_to_flambda_primitives.ml:113-119`). In Flambda 2 the
     store is an `Array_set` behind an `Opaque_identity`
     (`:2607-2622`), not a `Block_set`. R2-18.
  6. **Recursive values** (`value_rec_compiler.ml:57-78, 165-166`):
     `let rec x = C (..., x)` allocates with `caml_alloc_dummy` and
     fills with `caml_update_dummy`, which are C functions; the block
     is then read as what it is, with `Reads_agree` where its fields
     are immutable. Flambda 2 sees two calls of external functions.
     X5 has read `value_rec_compiler.ml` for Lambda that is not legal
     with respect to mutability, which the human suspected, and found
     nothing: the placeholder is not read before it is filled.
  7. **Recursive modules** (`translmod.ml:509, 542`): each module of
     a recursive group is allocated as a placeholder by
     `CamlinternalMod.init_mod`, and `CamlinternalMod.update_mod`
     overwrites its fields once the module is built ("backpatching",
     in the file's own words). These are functions of the run-time
     library; Flambda 2 sees two calls. Unlike 6, **a field may be
     read before the update**, and the fields are read as immutable.
     It is miscompiled today: a field read before and after
     `update_mod` gives the value from before (X5-2).
  Modules that are not recursive are made by
  `Pmakeblock (0, Immutable, ...)` and nothing is stored into them.
  Overwriting a unique value in place (`Texp_overwrite`) is not
  implemented (`translcore.ml:1614-1617`); it will be an eighth.
- So a field that is stored into and later read as immutable arises in
  4, 5, 6 and 7, and in unsafe code. In 4, 5 and 6 every store comes
  before every read of the block that is stored into. **In 7 it does
  not**: a read may come first, so no rule of the kind "stable from
  the first immutable read" holds of recursive modules. In 4 the
  stores are marked `Assignment`: **the mark `Initialization` does
  not tell an initialising store from a mutation**. The human has
  ruled 4 and 5 out of the model (decision 4). 6 and 7 reach Flambda
  2 as calls of functions outside the unit, which the model does not
  have; 7 is named in decision 4 as outside what any stage covers.
- *Unboxing.* `simplify/unboxing/unboxers.ml:227` makes a `Block_load`
  marked `Immutable` at each use of a continuation whose parameter is
  unboxed, on paths where the handler may have had no such load. It
  does so only for a parameter whose type proves one tag and an exact
  size (`optimistic_unboxing_decision.ml:98, 108`;
  `Provers.prove_unique_tag_and_size`, `prove_variant_like`). A type
  learnt from immutable loads says "at least so many fields" and does
  not qualify (`Row_like_for_blocks.get_singleton` answers `None` on
  `At_least`), and `Mutable_block` never does. An exact size comes
  from an allocation, so **unboxing adds immutable loads only to
  blocks made `Immutable` or `Immutable_unique`**, never to a block
  made `Mutable`.

### 1.5 What the first version models

In: `Make_block` of values at the three mutabilities on the heap;
`Block_load` and `Block_set` at the access kind `Values`; `Get_tag`,
`Is_int`, `Is_null`, `Opaque_identity` and `Phys_equal` on what they
make. This is `ref`, records all of whose fields are mutable, and
extension constructors. The reasons for the cut:

- Each of arrays, bytes, float blocks and mixed blocks is another form
  of cell and its own primitives, with nothing new for the design:
  nothing outside the heap's own files is to match on a cell (section
  2.3), so each is leaf work, as a primitive is after C1.
- Atomics need a model of concurrency, and bigarrays and `Peek`/`Poke`
  a model of memory outside the OCaml heap. Lazy blocks change tag when
  forced (the one place where a tag is not immutable).
- Static blocks that are not `Immutable` need symbols to be addresses
  of cells (section 2.7). The compiler itself makes a static block only
  by reification, so `Immutable` or `Immutable_unique`; a `Mutable` one
  can be written in fexpr only (as far as I read).
- Local allocation. Regions are a second store with a stack
  discipline, and a use after `End_region` is undefined; modes are
  annotations on allocations and on assignments. The design below does
  not preclude them (a region would be a second sort of name, and a
  cell would say which region it is in), but nothing here is designed
  for them. The cost for the corpus is real: the front end puts a
  region around any function that may allocate locally. Hence the
  interim conversion decided overnight (D37): regions are dropped and
  a local allocation is read as one on the heap, so that a local
  `ref` or record is a cell like another. That is sound for a program
  that the type checker accepts, since the model never frees a cell;
  it says nothing of lifetimes, and a full model of regions would
  replace it.

Not modelled, and no plan to: the garbage collector, running out of
memory (allocation always succeeds, as the compiler assumes),
finalisers, signals.

## 2. The store

### 2.1 What has an identity

The question under D2 and D19. Options:

- (a) **Only what the compiler says has one**: blocks (later arrays,
  bytes) made `Mutable` or `Immutable_unique`. An immutable block, a
  boxed number and a closure stay values that are their contents, as
  C1's stage 3 and C3 have them.
- (b) **Every allocation is a cell**: `Make_block`, `Box_number` and a
  set of closures all return a location. One uniform notion, close to
  the machine.
- (c) (a), with closures as cells too.

Recommendation: (a). Why:

- Under (b) the model distinguishes two equal immutable blocks, and
  Simplify does not preserve that: CSE of `Make_block` and
  `Box_number`, lifting with sharing, unboxing a parameter and boxing
  it again, and the "`Some x -> Some x`" equation
  (`simplify_immutable_block_load0`) all change how many allocations
  there are and which is which. Every one of them would have to be
  justified by an exit relation that forgets the identity of immutable
  cells, and `Phys_equal` would have to be made insensitive to it
  anyway. (b) buys nothing that (a) lacks, at the price of putting
  every block of every existing statement in the heap.
- Under (a) nothing that exists changes meaning: `Value_block`,
  `Value_boxed_number`, the closures, the four observations and C3's
  design stay as they are, and the observations do not read the heap.
  A type's denotation does take the heap (an immutable block may hold
  a location, and `Mutable_block` and unique `Variant` types are about
  cells; section 7.2), but what a type says of the fields of an
  immutable value itself cannot be invalidated by a write, by
  construction; under (b) that would be a frame lemma to prove for
  every type.
- Closures: `Mutability` does not apply to them, the compiler lifts
  and duplicates them (a closed set is lifted from inside a function),
  and `prove_physical_equality` answers on two closures only by their
  names (the same alias, or two different symbols), never by what they
  are. So no identity; this is C3's recommendation on D2.

What (a) costs: `Phys_equal` of two immutable allocated values has no
faithful deterministic meaning (section 2.6).

### 2.2 Locations

Options:

- (a) **A location is a name.** `location := positive`, compared with
  `Pos.eqb` only. Allocation takes `fresh_location heap`, a function
  whose one property is that its result is not in the domain of the
  heap; it is opaque after that lemma. Two runs that allocate in a
  different order, or a different number of times, get different
  names, and are related by a bijection on locations (section 3).
- (b) **A location is a number**, the next one: the n-th allocation is
  at n. The same machine as (a) with `fresh_location` transparent.
  Proofs can then compute addresses, and nothing stops a statement from
  depending on allocation order.

Recommendation: (a). It is the nominal treatment the human asked for
(D29), and (b) gains nothing: the bijection is needed in either case,
as soon as a rewrite deletes an allocation.

Agreed with N1 (recorded in `status/C4.md`):

- Locations are an instance of N1's generic interface
  (`FlambdaNameAbstractionSpec.v`), which takes one sort of name at a
  time. The action is a separate family of functions that
  take a `FlambdaNominalSpec.permutation` of locations; `renaming`
  (variables and continuations) gains no field. Terms hold no location
  and values hold no variable or continuation, so the two actions never
  meet, and N1's `apply_renaming_state` leaves the heap alone:
  `step_equivariant` for variables and continuations survives with one
  trivial case for each new construct.
- An instance provides `apply_renaming`, `free_names` and `equal` (for
  a heap, `map_equal`), with the laws N1 lists (group action, the
  action respects `equal`, free names are permuted, and the support
  law: a permutation that fixes the locations of a thing fixes the
  thing).
- `fresh_location` is N1's `fresh_name` on the domain of the heap, the
  only function that looks at numbers. The prototype defines it so:
  `fresh_location h := fresh_name (domain h)`.
- `step` is a function, and is equivariant for locations up to the
  choice of the fresh name:
  `step (π · s) = Step s1 -> step s = Step s2 -> ∃ π', π' agrees with π
  on the locations of s ∧ s1 = π' · s2`. N1: this is the usual form for
  a function that makes a name; it lifts to `run` by composing the
  extensions. This is about whole states. Its link with the relation
  at exit is on what the exit values reach only: the relation does not
  see garbage, so it is not "the two heaps are in one orbit" (two
  exits with no values and different heaps are related).
- Symbols and code ids are global and have no action. Relating the
  static names of two units is a relation carried by the comparison
  (section 3), not a renaming.

### 2.3 Cells and the heap

```coq
Definition location : Type := positive.

Inductive value : Type :=
  ...
  | Value_location (l : location).       (* kind [Value] *)

(* [Mutability.t] without [Immutable]: what a cell may be. *)
Inductive cell_mutability : Type :=
  | Cell_mutable
  | Cell_immutable_unique.

Inductive cell : Type :=
  | Cell_block (mut : cell_mutability) (tag : Z) (fields : list value).

Definition heap : Type := finite_map cell.   (* FlambdaMapSpec *)

Record state : Type := State {
  state_expr : expr;
  state_vars : env;
  state_conts : cont_env;
  state_statics : static_env;
  state_heap : heap
}.
```

- A cell holds values, which may be locations: the heap is a graph and
  may be cyclic. A field holds a value of kind `Value` (the machine
  tests it where a cell is made or written, as C1's `Make_block` does:
  a mismatch of kinds is undefined where executed). The tag and the
  number of fields of a cell never change.
- A write is a new binding in front (`(l, c) :: h`): the first binding
  of a name wins, so equality of heaps is `map_equal`, not `=`.
- The heap only grows: there is no deallocation and no collection. So
  a location that is bound stays bound, and a state reached from a
  term has no dangling location (section 6: the invariant and its
  preservation).
- No variable and no continuation is in a cell.
- `Value_location` is read through one new observation,
  `cell_of heap v : option cell`. The four observations of
  `FlambdaValueSpec.v` and `is_allocated` do not change, and answer
  `None` and false on a location: a mutable block is not a `block_of`.
- A primitive that is given a location to read (a unary primitive, a
  load, a write) reads the heap, and has no value on a location that
  is not bound. This is the human's ruling on symbols (D8) applied to
  locations; a term cannot mention a location, and no state reached
  from a term has one that dangles (section 6). The rule is for every
  primitive and every argument, whether or not the primitive would
  read the cell: `exec_prim` tests it before anything else (section
  2.5), so `Phys_equal` compares no location that dangles and
  `Make_block` stores none.
- Nothing outside the heap's own files is to match on `cell`: a cell is
  read through `cell_of` and through observations that give its tag
  and its fields. So a later form of cell (an array, bytes), or more
  recorded in a cell (decision 4), changes the heap's files only. T1
  asked for this, and for one observation that answers for "an
  immutable block, or a cell that is a block", by tag and fields
  (`block_or_cell_of statics heap v`), for `Is_int` and `Get_tag`.

Where the heap goes in a state is decision 8: a fifth field, as above,
or the heap and the static environment under one field.

### 2.4 `step` stays a function

The `Let` case of `step` runs `exec_named statics heap vars
defining_expr : option (value * heap)`, which is `exec_prim` on a
primitive and `eval_named` with the heap returned as it came on
everything else; `eval_named` stays, with the lemmas about it. Nothing
else in `step` changes but the extra field. Allocation is
deterministic through `fresh_location`. So `run`, `behaves`,
`behaviour_unique_statement` and the extracted machine of the test tool
are as they are.

### 2.5 The primitives

Options:

- (a) **Two layers.** `eval_prim statics p vs : option value` is
  unchanged, with its four laws, for the primitives that neither read
  nor write the heap. Over it,
  `exec_prim statics heap p vs : option (value * heap)`: on a primitive
  of the heap (and on `Get_tag` and the like applied to a location) it
  is defined directly; on anything else it is `eval_prim` with the
  heap returned as it came.
- (b) **One function**: `eval_prim` itself takes and returns a heap.
  Every law of C1 is restated, and every use of `eval_prim` (the
  folding of constants, the three proofs that use the first law)
  changes.

Recommendation: (a): it adds and does not change, and a primitive of
the heap stays leaf work in the primitives' files.

**Names bound to nothing.** A primitive has no value when one of its
arguments is a symbol or a location that is bound to nothing. For
symbols this is the human's ruling on D8 ("any operation on such
symbol should be undefined behaviour"), which C1 has since given
`eval_prim` as a law (`eval_prim_symbols_bound_statement`, on the
integration branch); for locations it is decision 12. `exec_prim`
tests it first, for every primitive:

```coq
Definition argument_bound (statics : static_env) (h : heap) (v : value)
    : bool :=
  match v with
  | Value_symbol s => is_bound s (static_values statics)
  | Value_location l => is_bound l h
  | _ => true
  end.

Definition exec_prim (statics : static_env) (h : heap) (p : prim)
    (vs : list value) : option (value * heap) :=
  if forallb (argument_bound statics h) vs
  then exec_bound_prim statics h p vs
  else None.
```

So an allocation and a `Block_set` take no such name, although they do
not read what it is bound to, and `Phys_equal` compares no location
that dangles. Proved in the prototype: `exec_prim_symbols_bound`
(C1's law, of `exec_prim`) and `exec_prim_locations_bound`. As in
C1's law, only the arguments themselves are tested, not the names in
their fields; that there is none there either is the invariant of
states (section 6). With C1's law the test on symbols is redundant for
the primitives that go to `eval_prim`; in the prototype, whose base
is older than the law, it is what makes the statement true of them.

The primitives of the first version. "No value" is undefined.

- `Make_block (Block_kind_values tag) mut`. `Immutable`: as C1, a
  `Value_block`. `Mutable` or `Immutable_unique`: a new cell holding
  the arguments, and its location. No value if an argument is not of
  kind `Value`.
- `Block_load kind mut field`. On an immutable block (a `Value_block`
  or a symbol bound to a static block): C1's, whatever `mut` says. On
  a location: the field of its cell now, under C1's checks (tag, size,
  bounds, `Immediate`); but a load marked `Immutable` or
  `Immutable_unique` from a `Cell_mutable` cell has no value
  (decision 4).
- `Block_set kind init field`, of a block and a new value: on the
  location of a `Cell_mutable` cell, with the field in bounds and the
  new value of kind `Value` (a tagged immediate if the access kind
  says `Immediate`), the heap with that field replaced, and the value
  unit. No value on anything else: an immutable block, a symbol, a
  unique cell (decision 5). `init` does not affect execution; the
  only stores marked `Initialization` are those of tail-modulo-cons
  (section 1.4), which the conversion refuses.
- `Get_tag` of a location: the tag of its cell. `Is_int` of a
  location: 0, with or without `variant_only` (a mutable block is a
  block; `prove_is_int` says so). `Is_null`: 0. `Opaque_identity`:
  itself.
- `Phys_equal`: section 2.6.

`Make_block` and `Block_load` gain the argument `mut`, which C1's
stage 3 left out by refusing every mutability but `Immutable`. That
changes two constructors of the primitives' own files; only the
conversion in the test tool uses them. The owner of the primitives
agrees to both, and to `exec_prim` being `eval_prim` by definition on
everything else, so that the laws of `eval_prim` (five now) carry over
by rewriting.

In the prototype the four new primitives are under one extra
constructor of `prim`, `Heap`, so that no existing constructor
changes; that is for the prototype only. `Phys_equal` on immediates
needs no heap and is being added to the primitives' files now
(section 2.6).

### 2.6 `Phys_equal`

The compiler compiles it to a comparison of machine words. The OCaml
manual says of `==` that on mutable values it is identity, and on
immutable ones implementation-dependent, with only "`e1 == e2` implies
`compare e1 e2 = 0`" guaranteed; `Mutability.Immutable` says the same
("share or duplicate at will"). Simplify uses that freedom (section
1.4). CSE and the sharing of lifted constants make two equal immutable
values the same, turning a false into a true (C4-3). It also decides
by names: the same alias is equal, and two different symbols are
different, whatever they are bound to. So after Simplify two static
blocks with equal contents compare unequal: R2's term returns `(1, 0)`
for a symbol against itself and against another bound to an equal
block (R2-21).

So the honest meaning of `Phys_equal` on two immutable allocated
values with equal contents is "either answer", and the machine is a
function. Options:

- (a) **No value on anything allocated** (D19's recommendation).
  Nothing to design; but `==` on a `ref` is then undefined, which the
  heap exists to give a meaning to.
- (b) **Defined except on two immutable allocated values.** Two
  immediates or nulls: equality. An immediate or null against anything
  allocated: false. Two locations: whether they are the same location.
  A location against an immutable allocated value: false. Two
  immutable allocated values (blocks, boxed numbers, closures,
  strings, symbols bound to them): no value. No value on poison or on
  a symbol that is not bound.
- (c) (b), and false on two immutable allocated values that cannot be
  equal by their first layer (different tags or sizes, a block against
  a boxed number). This follows the "proved false" cases of
  `prove_physical_equality`; each is one more place where the model
  and the prover must agree.
- (d) **By contents**: true on two immutable values exactly when their
  contents are equal. Deterministic; but it is not what runs (the
  machine answers false on two separate equal allocations), equality
  of contents through cyclic static data is not a structural
  recursion, and **Simplify does not preserve it**: it folds the
  comparison of two different symbols to false, where equality by
  contents says true when they are bound to equal blocks (R2-21). The
  second version of this request said the opposite, wrongly. Under
  (d) the model would refute a rewrite that the compiler makes.
- (e) **Either answer**, properly: the machine takes an oracle for
  these comparisons and refinement quantifies over it (for every
  oracle of the target there is one of the source). Faithful. It
  changes `state`, `refines` and every proof about a rewrite that
  deletes, duplicates or moves a `Phys_equal`.

Recommendation: (b) now. It gives `==` its meaning on what has an
identity and on immediates, which is where the language defines it.
On two immutable allocated values it gives none, and that includes
comparisons that Simplify does decide (the same alias, two different
symbols, two blocks of different tags): under (b) those rewrites are
validated only vacuously, since the source is undefined. This is
weaker coverage, not a faithful account of an answer that the
language leaves open, and D22's caution applies in full: library code
does compare immutable values with `==` as a fast path, and nothing
is proved of a program from such a comparison on. (c) is leaf work if
the corpus asks, and recovers the cases proved false by shape. (e) is
the faithful one, and is for the human to want: it is what puts
programs that compare immutable values physically inside the
theorems. D30 (physical equality of immutable data inside the
compiler "is probably a bug") is about the compiler's own code, and
is no reason to leave the program's `Phys_equal` without a meaning.
The CR that (b) carries is in the list of decisions. The owner of the
primitives, who wrote D19's recommendation before there were
locations, agrees with (b).

**On immediates, now.** Integer `=` and `<>` reach Flambda 2 as
`Phys_equal` (V2's examples from OCaml), so no source program with an
integer equality can be checked until it has a value on immediates.
That part needs no heap and no decision: on two tagged immediates it
is equality, and an immediate against an allocated value is false
under every option but (a). P1 is adding it to the primitives' files
now, as a binary primitive of `eval_prim`, with the prototype's names
(`equality_comparison`, `Phys_eq`, `Phys_neq`) and a CR naming D19.
The heap then adds, in `exec_prim`, the cases with a location; the
case of two immutable allocated values stays without a value until
decision 3 is taken.

Under every option but (a) the answer on two locations is by their
names, so it is the same on both sides of a correspondence: this is
why the correspondence must be a bijection on what has identity.

### 2.7 Later: symbols as addresses

A static block that is `Immutable_unique` or `Mutable` has an identity
too, and its address is its symbol. Simplify lifts an
`Immutable_unique` block made at toplevel to such a symbol, so
validating a unit that defines an exception will need it. The design
that fits: an *address* is a location or a symbol; a cell lives at an
address; the correspondence of section 3 relates addresses, and its
part between a location of the source and a symbol of the target is
what lifting needs. The first version has cells at locations only, and
the conversion refuses static blocks that are not `Immutable`. N1
agrees that symbols get no renaming action: the address relation is
carried by the comparison.

## 3. What is observed at exit, and refinement

### 3.1 An exit carries the memory

Today `Exit k vs` holds the values, and `refines` compares them with
`=`; a symbol among them is compared by its name and what it is bound
to is not looked at. With a heap that is not enough for a unit run on
its own: its result is typically a pointer, and what the pointer
reaches must be part of the observation, or a wrong write just before
the exit would go unseen.

```coq
(* What is observed when a state leaves through an unbound
   continuation: the arguments, and the memory they point into. *)
Record outcome : Type := Outcome {
  outcome_values : list value;
  outcome_statics : static_env;
  outcome_heap : heap
}.

Inductive step_result : Type :=
  | Step (s : state)
  | Exit (k : continuation) (o : outcome)
  | Undefined.

Inductive behaviour : Type :=
  | Exits (k : continuation) (o : outcome)
  | Goes_wrong
  | Diverges.
```

`behaves` and `behaviour_unique_statement` keep their text: a state
still has at most one behaviour, exactly.

### 3.2 The relation on outcomes

Two outcomes are related when there is a *correspondence* between
their memories under which their values agree.

```coq
Record correspondence : Type := Correspondence {
  corr_locations : location -> location -> Prop;
  corr_values : value -> value -> Prop
}.
```

`corr_locations` says which location of the first run is which of the
second. `corr_values` is a set of pairs of values that are taken to be
the same, each to be justified one step at a time: it is a
bisimulation, and it is what lets cyclic immutable data be compared.

One step, `value_step poison_refines r statics statics' R v v'`
(`FlambdaHeapSpec.v`): `v` and `v'` have their heads in common, and
`R` holds of what they hold. Its rules:

1. A constant and the same constant.
2. `Value_location l` and `Value_location l'` when
   `corr_locations r l l'`.
3. Immutable values, by their contents, read through the observations
   (so through a symbol, on either side): two values that `block_of`
   sees as blocks of the same tag, with fields related by `R`
   pairwise; two that `boxed_number_of` sees as boxed numbers whose
   contents are related (`contents_related`: the same number, or with
   rule 5 a poison and a number of its kind); two that `string_of`
   sees as the same bytes; two that `closure_in_set` sees as closures
   at the same function slot of sets with the same code ids, whose
   value slots are related by `R` pairwise, and whose closures at the
   other function slots are related. The last is asked in one of two
   ways. Either the two sets are known in full (`set_bound`: the
   closure was made by a `Let` and holds its set, or it is a symbol
   of a static set each of whose symbols is bound to the closure of
   the set at its slot); then the closures at the other slots are
   closures of the same two sets, and are related by this rule. Or a
   function slot can be projected from both closures or from neither,
   and the two projections are related by `R`. The second way is for
   a static set that is not bound in full, of which nothing is known:
   a projection from its symbol gives the symbol that the set names,
   whatever that is bound to (D4). `related_projections` is the
   consequence: where a function slot can be projected from the first
   of two related values, it can from the second, to a related value.
4. A symbol and the same symbol, when it is nothing that can be read
   in either memory (a symbol that is not bound, as one of another
   unit).
5. (Optional, decision 6; the flag `poison_refines`.)
   `Value_const (Poison kind)` and any value of kind `kind`.

(The prototype has two more rules, for values that no observation
reads: a `Value_boxed_number` whose contents are not of a kind that
has a boxed form, and a `Value_closure_of_set` at a function slot that
its set has not got. Each is itself.)

`value_related poison_refines r statics statics' v v'`: the pair is in
`corr_values r`, or `v` and `v'` are one step apart with
`value_related` on what they hold. It is a plain inductive definition.

`correspondence_valid poison_refines r statics statics' h h'`:

- `corr_locations r` is a partial bijection (two pairs have the same
  first component exactly when they have the same second);
- two locations that correspond are bound to cells of the same
  mutability and tag whose fields are related pairwise;
- two values in `corr_values r` are one step apart, with
  `value_related` on what they hold.

`outcome_related poison_refines o o'`: there is a valid `r` under which
the values of `o` and of `o'` are related pairwise. `outcome_refines`
is it with rule 5 and `outcome_equivalent` without.

A correspondence is a pair of relations and not of lists, since it is
never computed: the identity is then `eq`, with nothing to enumerate.

**Why the correspondence is on values.** The second version had
`corr_symbols : symbol -> symbol -> Prop` where this one has
`corr_values`, and a rule for a symbol against a symbol. That relation
is not transitive. Take three memories with cyclic static blocks, out
of phase:

- in the first, `s` is bound to
  `Static_block 0 [Value_block 0 [Value_symbol s]]`, and the value at
  exit is `Value_symbol s`;
- in the second, `u` is bound to `Static_block 0 [Value_symbol u]`,
  and the value is `Value_symbol u`;
- in the third, `t` is bound to
  `Static_block 0 [Value_block 0 [Value_symbol t]]`, and the value is
  `Value_block 0 [Value_symbol t]`.

Each is the infinite chain of blocks of tag 0 with one field. The
first was related to the second (pair `s` with `u`) and the second to
the third (pair `u` with `t`), but not the first to the third:
unfolding the two never arrives at two symbols at once, so there is
no pair of symbols to give and no finite derivation. A relation
between symbols cannot say "the symbol `s` is the block
`Value_block 0 [Value_symbol t]`". A relation between values can, and
two such correspondences compose: pair `v1` with `v3` when some `v2`
is related to both.

R2 found a second failure in the second version, with rule 5: an
inline boxed number had to hold the same constant as its counterpart,
where a static one had its contents related recursively, so a boxed
poison was refined by a boxed number only when it was static. Now
both presentations go through `boxed_number_of` and one relation on
the contents.

Proved of it in the prototype:

- `outcome_related_reflexive`: a closed outcome is related to itself;
- `outcome_related_transitive`: the relation composes, with rule 5 and
  without (the two correspondences are composed; 150 lines with the
  lemma on one step);
- `outcome_equivalent_refines`: the relation without rule 5 is included
  in the one with it;
- `location_names_not_observed`: a pointer to a cell at one location is
  a pointer to an equal cell at another;
- `aliasing_observed`: two pointers to two cells are not two pointers
  to one, even if the cells are equal;
- `block_and_symbol_related`: a block made by a primitive is a symbol
  bound to an equal static block (D6);
- `boxed_poison_refined`: a boxed poison is refined by a boxed number
  of its kind, with the symbol on either side (R2's example);
- `garbage_not_observed`: a cell that nothing reaches does not count;
- `delete_write_wrong`: a `Block_set` deleted is seen (section 4).

Why it has this shape:

- Rule 2 with the bijection is "the reachable graph up to a bijection
  on locations", which is what the plan asks for. Only what the exit
  values reach is constrained: a cell that nothing reaches is not
  observed, so an allocation that is not used may be deleted, and two
  allocations may be made in either order.
- The correspondence is given, not computed. The heap may be cyclic,
  and `corr_locations` is the bisimulation for it; static data may be
  cyclic too (a group of bindings may be recursive), and `corr_values`
  is the bisimulation for that. The relation on values is a plain
  inductive definition under the two.
- Immutable values need no bijection (rule 3): sharing them or not is
  not observed. This is what lets `Make_block` and a symbol bound to
  an equal static block be the same at exit.
- The link with N1's action is for a narrow case, and its exact
  premises are N1's to state with the theorem. The case I have in
  mind: no symbol and no poison in what the exit values reach, so
  that immutable values are compared structurally and static data
  plays no part; and the two heaps no more than what the exit values
  reach. Then the relation is the orbit relation of the action on
  locations: `∃ π, equal (π · (vs, h)) (vs', h')`. Outside that case
  it is coarser than any orbit, on purpose. It does not see garbage:
  two exits with no values are related whatever their heaps. And it
  does not see how immutable data is shared: a static block that
  points to itself and two static blocks that point to each other
  have the same unfolding and are related, though they are not
  isomorphic as graphs of named symbols (R2's example).

### 3.3 `refines` and `equivalent`

```coq
Definition behaviour_refines (b b' : behaviour) : Prop :=
  match b, b' with
  | Exits k o, Exits k' o' => k = k' ∧ outcome_refines o o'
  | Goes_wrong, Goes_wrong | Diverges, Diverges => True
  | _, _ => False
  end.

Definition refines (source target : state) : Prop :=
  (∀ (k : continuation) (o : outcome),
    behaves source (Exits k o) ->
    ∃ o' : outcome,
      behaves target (Exits k o') ∧ outcome_refines o o')
  ∧ (∀ b' : behaviour,
      b' <> Diverges ->
      behaves target b' ->
      (∃ b : behaviour, behaves source b ∧ behaviour_refines b b')
      ∨ behaves source Goes_wrong).
```

`equivalent` is the same shape in both directions with
`outcome_equivalent`. `expr_refines` and `expr_equivalent` quantify
over the heap as they do over the other environments, and (decision 9)
over closed memories only: no dangling location.

What must be proved in the core, and what it costs. Of it, the first
item is proved.

- `outcome_refines` and `outcome_equivalent` are reflexive on a closed
  outcome and transitive, and `outcome_equivalent` is symmetric: all
  proved in the prototype (section 3.2).
- Refinement is reflexive on a closed state (proved:
  `heap_refines_reflexive`). It follows from the lemma on related
  states, below, since a closed state is related to itself
  (`closed_state_related`); it does not need that a step keeps a
  state closed. That invariant (section 6) is proved too
  (`heap_step_closed`), and is what the rewrites use that need the
  state after a step to be closed (CSE, exchanging two bindings).
- `refines_defined_statement` and `refines_antisymmetric_statement`.
  The second needs that mutual refinement gives the symmetric
  relation; with rule 5 that is an argument about the reachable part.
- Every existing rewrite, in one lemma. Keep today's definition as
  `refines_exactly` (exits with equal values and equal heaps), and
  prove once that a closed source that is refined exactly, by a target
  that binds the same symbols to the same static values, is refined:
  such outcomes are related by the identity. A theorem that exists is
  then carried over by that lemma with its proof untouched, since none
  of the rewrites that exist changes the heap. There are two
  exceptions, each a rewrite whose target does not bind the symbols
  that its source binds.
  - The two statements about static bindings that are dropped
    (`drop_statics_refines` and its corollary): their target binds
    fewer symbols, and they need the correspondence that is the
    identity on the symbols kept, which their premise `envs_free_of`
    supplies.
  - Lifting, as V3 validates it on today's model (`lift_unit`, with
    `lift_unit_program_refines`; on V3's branch as this is written,
    and approved by R2 for today's exits). Its target binds more
    symbols. Today an exit is compared by its values as they are, and
    what a symbol is bound to is not compared, so V3's check need not
    ask that the unit never names the symbol that it lifts to. Under
    the relation of section 3.2 it must. R2's example: a unit makes a
    closure one of whose value slots is a symbol that the unit does
    not bind, puts the closure in the block of the module, and exits
    with the symbol of that block; the closure is lifted to the very
    symbol that its value slot names. The two exits are the same
    symbol. But the first block holds a closure whose slot is a
    symbol bound to nothing, and the second a symbol bound to a
    closure whose slot is that closure itself: the relation, which
    reads through symbols, does not relate them, and should not.
    `lift_closure` excludes the case by its premise
    `value_slots_avoid`, with the other premises that the symbol is
    new (section 4.2). So when the observation changes, V3's checked
    function gains the test that the unit does not name a symbol that
    it lifts to (or has it from the condition of well-formedness on
    symbols, C0's follow-up to D8, if that says enough), and its
    theorem is proved again with `machine_respects_relation_except`.
    `validate_unit_sound` and `lift_unit_program_refines` keep their
    shape: unconditional of a result that was checked.
- **The new lemma: the machine respects the relation.** If two states
  run the same expression under related environments, continuations
  and memories, their behaviours are related. This is what
  `plug_refines` needs as soon as a hole is entered twice: the second
  time, the two sides arrive with memories that are related and not
  equal, and the premise `expr_refines source target` speaks of equal
  ones. **It is proved in the prototype**, for the prototype's machine
  and the relation without rule 5 (`heap_run_related`,
  `machine_respects_relation`; 2,000 lines of `FlambdaHeapProofs.v`):
  - the relation on states (`states_related`): the same expression;
    the same code; the same symbols bound; a correspondence, valid
    without rule 5, in which every symbol corresponds to itself (the
    expression may name any); environments that hold related values
    for the variables that are free in what will run, so that a
    binding that is not used may be on one side only; continuations
    related closure by closure;
  - a step of the source is a step of the target to related states,
    with the correspondence extended by a pair of locations at an
    allocation; an exit is an exit with outcomes related by
    `outcome_equivalent`; where the source is undefined nothing is
    asked. As the machine is a function, this forward direction gives
    both clauses of `refines`;
  - every primitive respects the relation (`related_exec_prim`: on
    related arguments and memories, related results and memories, or
    no value in the source), by cases on the primitive, so that a
    primitive added later proves its case;
  - `Let_static` was the hard case, as expected: the two static
    environments grow by bindings whose values are related, and the
    correspondence is shown valid again for them. It is what needs
    every symbol to correspond to itself.
  What is left of it for the core. Today's
  `FlambdaContextProofs.transfer` is this lemma for "equal values,
  related code"; the two are to be one lemma, for related values and
  related code, in the real state. And with rule 5 it is a second,
  later lemma: the source's poison is then anything in the target, and
  each primitive must be undefined on a poison it inspects, which is
  so today.
- Why quantifying over all continuations still suffices for contexts:
  a context is, at the hole, a continuation environment, and
  `expr_refines` holds under every one. So what a context can reach
  through its own variables after the hole exits is covered by the
  premise, and the relation at exit need not mention the initial heap.

### 3.4 `validate_unit_sound`

It says that a validated unit, run from empty environments, is refined
by its simplification. With the change: from the empty heap as well,
and with the new `refines`: the two runs leave through the same
continuation with outcomes related by a correspondence. That is a
change of what the theorem says, in the direction of saying more about
the memory and less about names of locations and of lifted symbols.

### 3.5 How one relation serves D1, D6 and D26

- **D6** (a block made by `Make_block` against a symbol bound to an
  equal static block). Served by rule 3. Cost: the rule, and that no
  primitive tells the two apart: true today, as every reading goes
  through an observation, and kept by `Phys_equal` having no value on
  two immutable values (under option (c) or (d) of 2.6 it would have
  to be checked again). Lifting can then be stated at all. The
  statement of section 4.2 is the refinement; the converse, which
  would make it an equivalence, is a second statement and is not
  written. What the rule does not give by itself: lifting of an
  `Immutable_unique` block (section 2.7).
- **D26** (a name that holds poison replaced by a real value). Served
  by rule 5, in `refines` only, and inside a boxed number by the
  relation on its contents (a boxed poison, inline or static, is
  refined by a boxed number of its kind). Cost: the relation is no longer
  symmetric, so there are two (`outcome_refines`,
  `outcome_equivalent`); every primitive must be undefined on a poison
  that it inspects, which C1 already has (`Is_int`, `Is_null`,
  arithmetic, `Switch`, a call), and may pass one along
  (`Make_block`, a closure, `Opaque_identity`, `Apply_cont`); and
  antisymmetry is harder. It can land after the rest: it is one rule.
- **D1** (what an exit observes of a closure). The relation observes
  the whole closure, as today: slot, code ids, value slots (which now
  may hold locations, related by rule 2). A weaker observation is a
  third component of the correspondence, a relation on code ids with
  its own validity condition ("the two codes refine each other"),
  which is S4's to define; the shape leaves room for it and I do not
  design it.

## 4. What Simplify needs to be provable

All of this is in `FlambdaHeapSpec.v`, over the prototype's machine
(`heap_state`, `heap_step`, `heap_refines`, `heap_expr_refines`: the
machine of `FlambdaSemanticsSpec.v` with a heap, and refinement up to
the relation of section 3).

### 4.1 The laws of the classification

`effects_of_prim` and `coeffects_of_prim` are transcribed from
`Flambda_primitive.effects_and_coeffects`. What ties them to
`exec_prim` is one definition and four laws, each proved by cases on
the primitive, so that a primitive added later proves its case and
nothing else changes.

```coq
(* What a run may do to a heap: a cell that is bound stays bound, with
   its mutability, its tag and its number of fields, and with its
   fields if it is not mutable. *)
Definition heap_evolves (h h' : heap) : Prop :=
  ∀ (l : location) (mut : cell_mutability) (tag : Z) (fields : list value),
    lookup l h = Some (Cell_block mut tag fields) ->
    ∃ fields' : list value,
      lookup l h' = Some (Cell_block mut tag fields')
      ∧ length fields' = length fields
      ∧ (mut = Cell_immutable_unique -> fields' = fields).
```

- `exec_prim_evolves`: every primitive leaves a heap that the one it
  was given evolves to. With it, `heap_step_evolves`: so does every
  step.
- `no_effects`: `effects_of_prim p = No_effects` and
  `exec_prim statics h p vs = Some (v, h')` give `h' = h`.
- `only_generative_effects`: with `Only_generative_effects mut`,
  either `mut = Immutable` and `h' = h`, or the value is
  `Value_location (fresh_location h)` and `h'` is `h` with one cell
  bound to that location in front.
- `no_coeffects`: a primitive with neither effects nor coeffects that
  has the value `v` in `h1` has the value `v` in every `h2` that `h1`
  evolves to. This is "may be run later" and "may be run once in place
  of twice". It is not "may be run earlier": it says nothing of a heap
  that `h1` did not evolve from, nor of whether the primitive has a
  value before a branch that makes it meaningful. The compiler has a
  separate classification for that (`Validity`, section 1.1: every
  primitive is `Can't_move_before_any_branch`), which is not
  transcribed, and nothing here licenses moving a primitive before a
  branch.

And the law that says the classification is not vacuous:
`mutable_load_not_stable`: the load marked `Mutable` (no effects, has
coeffects) has two different values in two heaps of which the first
evolves to the second. So it is not to be shared with an earlier one.

`heap_evolves` is also what the types need (agreed with T1): whatever
a type says of a location must be preserved by it, so a type may speak
of the fields of a cell only if the cell is not mutable.

### 4.2 The statements, against the design

Each is proved in the prototype. I
checked each by hand against the cases of the machine; doing so I
corrected two (a lifted symbol has to be new for the body and for the
state, not only unbound; the lemma on related states needs every
symbol to correspond to itself).

**Deleting a binding** (`simplify_let_expr.ml`). The compiler's test,
exactly: at most generative effects, variable not used. No premise on
coeffects, none on the primitive having a value.

```coq
Definition delete_unused_let_statement : Prop :=
  ∀ (x : variable) (x_kind : flambda_kind) (p : prim) (args : list simple)
    (body : expr),
    at_most_generative_effects p = true ->
    var_free_b x body = false ->
    heap_expr_refines (Let x x_kind (Prim p args) body) body.
```

Proved (`delete_unused_let`), from the lemma on related states: after
the binding is run, the source is related to the target by the
identity on the locations of the heap before it, the new cell
corresponding to nothing and the variable being needed by nothing.
It needs the relation as soon as `p` allocates: after the deletion
every later location of the target is another than in the source, and
the cell that the source made is garbage. It is a refinement and not
an equivalence where `p` may have no value. And
`delete_write_wrong_statement` (proved): there are `x`, `p`, `args`
and `body` with `x` not free in `body` for which it fails; `p` is a
`Block_set`. So the premise on effects is needed, and today's
`prim_may_fold`, which lets every primitive but `Opaque_identity` go,
has to become "no effects" when the primitives land, and "at most
generative" when the relation does.

One statement that exists has no such premise at all:
`FlambdaNominalSpec.unused_let_statement` erases any named expression
whose variable is not used ("it has no other effect, there being none
in this fragment"). With `Block_set` it is false, by the same witness.
It gains the premise when the primitives land (section 8.2).

**Exchanging two bindings.** Not something Simplify does (section
1.2), but what CSE across other bindings and unboxing come to.

```coq
Definition exchange_lets_statement : Prop :=
  ∀ (x y : variable) (x_kind y_kind : flambda_kind) (p q : prim)
    (args_p args_q : list simple) (body : expr),
    effects_of_prim p = No_effects ->
    coeffects_of_prim p = No_coeffects ->
    x <> y ->
    var_in_simples x args_q = false ->
    var_in_simples y args_p = false ->
    heap_expr_refines
      (Let x x_kind (Prim p args_p) (Let y y_kind (Prim q args_q) body))
      (Let y y_kind (Prim q args_q) (Let x x_kind (Prim p args_p) body)).
```

`q` is any primitive, a write included: `no_coeffects` and
`exec_prim_evolves` are what make `p` have the same value after it.
Proved (`exchange_lets`): the two sides arrive at states that differ
in the order of two bindings only, which are related.

**CSE.** The second of two applications of a primitive to the same
arguments is the first. The compiler's condition
(`Eligible_for_cse`): no effects and no coeffects, or an allocation
whose result is immutable, with no coeffects.

```coq
Definition cse_adjacent_statement : Prop :=
  ∀ (x y : variable) (x_kind y_kind : flambda_kind) (p : prim)
    (args : list simple) (body : expr),
    (effects_of_prim p = No_effects
     ∨ effects_of_prim p = Only_generative_effects Immutable) ->
    coeffects_of_prim p = No_coeffects ->
    x <> y ->
    var_in_simples x args = false ->
    heap_expr_refines
      (Let x x_kind (Prim p args) (Let y y_kind (Prim p args) body))
      (Let x x_kind (Prim p args) (Let y y_kind (Simple (Var x)) body)).
```

Proved (`cse_adjacent`): the two sides arrive at one state, which is
closed. This is the case with nothing between the two; the general
one puts bindings between them and uses `no_coeffects` through
`heap_step_evolves`. For `Make_block ... Immutable` it holds because
such a block is a value: the two are the same value already. It does
not hold of the load marked `Mutable` (`mutable_load_not_stable`), nor
of `Make_block ... Mutable`, whose two results are two locations.

**Lifting an immutable block to a symbol** (D6).

```coq
Definition lift_block_statement : Prop :=
  ∀ (x : variable) (x_kind : flambda_kind) (s : symbol) (tag : Z)
    (fields : list simple) (body : expr) (vars : env) (conts : cont_env)
    (statics : static_env) (h : heap),
    lookup s (static_values statics) = None ->
    expr_avoids (Dropped [s] []) body = true ->
    binds_only_kept (Dropped [s] []) body = true ->
    envs_free_of (Dropped [s] []) vars conts statics = true ->
    heap_free_of (Dropped [s] []) h = true ->
    state_closed (Heap_state body vars conts statics h) ->
    heap_refines
      (Heap_state
         (Let x x_kind
            (Prim (Variadic (Make_block (Block_kind_values tag))) fields)
            body)
         vars conts statics h)
      (Heap_state
         (Let_static [Bind_symbol s (Static_const_block tag fields)]
            (Let x x_kind (Simple (Symbol s)) body))
         vars conts statics h).
```

The conditions on `s` are those of `FlambdaUnusedStaticsSpec.v` on a
name that is removed, read the other way. It needs rule 3 of the
relation, and that no primitive tells a block from a symbol bound to
an equal one. Nothing is asked of the fields: where one is a symbol
bound to nothing, or `s` itself, the `Make_block` has no value. It
says nothing of where the `Let` is: lifting from
inside a function also needs the `Let_static` to be moved to toplevel,
which is S5's. For an `Immutable_unique` block the statement is false
from inside a function (discrepancy C4-1), and at toplevel it needs
symbols as addresses (section 2.7).

It is proved. After one step of the first state and two of the
second, the two run the same body, and the second binds `s`, which the
first does not. `states_related` does not relate them: it asks that
the two states bind the same symbols and that every symbol corresponds
to itself. The prototype has a second relation,
`states_related_except D`, which leaves the symbols of `D` out of both
conditions and asks of each instead that the first state does not bind
it and that the second binds it to something allocated
(`names_related`); with no symbol left out it is `states_related`
(`states_related_nothing`). The machine respects it from a state whose
expression, handlers and code neither name nor bind a symbol of `D`
(`state_code_free_of`, an invariant that steps keep:
`heap_step_code_free_of`; then `machine_respects_relation_except`).
Nothing is asked of the values of the first state, and nothing needs
to be: a value related to a value of the second state cannot be a
symbol that is bound to nothing in the first and allocated in the
second. So the invariant is on syntax only, and the conditions
`envs_free_of` and `heap_free_of` of the statement are used once, to
relate the first two states.

The closure of one function is lifted in the same way
(`lift_closure_statement`, proved): `Let x = Set_of_closures code
value_slots` against a symbol bound to `Static_const_set_of_closures
code value_slots`. Its value slots may not name the new symbol, which
is a premise: nothing makes a closure undefined where one does.

So is a closure of a set of several functions
(`lift_closure_of_set_statement`, proved): `Let x = Closure_of_set
slot function_decls value_slots` against
`Let_static (bind_closures closure_symbols function_decls value_slots)`
and the symbol that `closure_symbols` has for `slot`. The whole set is
bound, with a new symbol for each of its functions; the symbols are
distinct, and all of them are left out of the relation. The closure
and its symbol are related by the first way of rule 3: the set of the
symbol is bound in full. Lifting a boxed number needs the same
relation and is not stated.

**A load from a block the types know.**

```coq
Definition load_known_field_statement : Prop :=
  ∀ (x b : variable) (x_kind : flambda_kind) (kind : block_access_kind)
    (field : Z) (known : simple)
    (body : expr) (vars : env) (conts : cont_env) (statics : static_env)
    (h : heap) (block loaded : value),
    lookup b vars = Some block ->
    eval_block_load statics kind field block = Some loaded ->
    eval_simple vars known = Some loaded ->
    state_closed (Heap_state body vars conts statics h) ->
    heap_refines
      (Heap_state
         (Let x x_kind (Prim (Unary (Block_load kind field)) [Var b]) body)
         vars conts statics h)
      (Heap_state (Let x x_kind (Simple known) body) vars conts statics h).
```

Proved (`load_known_field`): the two sides step to one state, which
is closed, and a closed state is refined by itself.

The second and third premises are what a `Variant` type that knows the
field says of `b` in an environment that satisfies it. They are about
the fields of an immutable value, so the heap is not in them and no
write between the place where the type was learnt and the load can
make them false. That is what keeping immutable blocks out of the heap
buys (section 2.1). What the field holds may be a location, and what a
type says of that does take the heap (section 7.2).

## 5. Names

What is agreed with N1 is in section 2.2. Written out:

- **What has an action.** A permutation of locations acts on values
  (`Value_location l` becomes `Value_location (π l)`, through blocks
  and the value slots of closures), cells, heaps (keys and contents),
  environments, continuation closures (their environments; C5's
  `Extra_args` form, which holds values, too), the values of the
  static environment, states, outcomes, step results and behaviours.
  It does nothing to terms, code, constants, kinds or primitives: none
  holds a location.
- **Free names.** `locations_of_value` (in the prototype), and the
  like for cells, heaps, environments and states, as sets of
  `FlambdaMapSpec.v`.
- **The laws of the instance**, for N1's interface: the action is a
  group action; it permutes free names; the support law, which for
  values is an equality proved by a short induction (`π` fixes
  `locations_of_value v` gives `π · v = v`). For heaps, equality is
  `map_equal`.
- **Statements owed.**
  `step (π · s) = Step s1 -> step s = Step s2 -> ∃ π', π' agrees with π
  on the locations of s ∧ s1 = π' · s2`, with the like for exits and
  for undefined; lifted to `run`; and on behaviours, that a state and
  its image under a permutation have outcomes related by
  `outcome_equivalent`. Then the theorem that links the two notions,
  in the narrow case of section 3.2 (no symbol and no poison in what
  the values reach, and nothing in the heaps but what they reach):
  there `outcome_equivalent` is `∃ π, equal (π · o) o'`. Its exact
  premises are to be fixed with N1.
- **Binders.** Allocation is the only binder of locations, and it is
  in the machine, not in a term. So no term form, no alpha-equivalence
  of terms and no scope rule changes.
- N1's `apply_renaming_state` (variables and continuations) leaves the
  heap alone, and a cell holds no variable or continuation.

None of this is in the prototype but `locations_of_value` and
`fresh_location` with its one lemma. It is leaf work in new files once
the heap is in the state, against N1's interface, which is on the
integration branch. N1 has said that it will state first, of the
prototype's machine, the part that concerns its own names: a renaming
of variables and continuations acts on the expression, the
environments and the code of a `heap_state`, leaves the heap and every
value alone, and commutes with `heap_step`.

## 6. Well-formedness

**Terms.** The heap adds nothing to `well_formed_unit`: no term
mentions a location. Two rows of C0's table widen without a new one:
the tags in range (row 8) are also those of a `Make_block` at any
mutability and of the access kind of a `Block_set`; and the
conversion's refusals (local modes, regions) are not conditions of
well-formedness but limits of the model.

No row for decision 4. What the compiler assumes and does not check
(C4-2) is that a field is not written after it has been read as
immutable, which is a property of a run and not of a term: the same
load and the same store are fine in one order and not in the other.
So it is the machine that enforces it, where executed (section 8.4),
and D32 allows the model to be that strict.

**States.** C0's note asks for one `well_formed_state`, with one part
for each condition that says something of a run. The heap's part is
`state_closed` (`FlambdaHeapSpec.v`):

- no location dangles: every location of a value in the environment,
  in the environments of continuation closures, in a cell or in a
  static value is bound in the heap;
- every field of a cell is of kind `Value`.

The second needs no premise on terms: the machine tests the kind where
a cell is made or written (D10, D16: a mismatch of kinds is undefined
where it is executed). With C2, "the fields of a cell are well-kinded
values" joins its `state_well_kinded`.

The statements:

```coq
Definition heap_step_closed_statement : Prop :=
  ∀ s s' : heap_state,
    state_closed s -> heap_step s = Heap_step s' -> state_closed s'.
```

It is proved (`heap_step_closed`), by cases on the step: every
primitive makes a closed value of closed arguments and keeps the
memory closed (`exec_prim_closed`), and a heap that evolves keeps
closed what was closed. With it, a unit run from empty environments
and the empty heap is closed at every state and at its exit.

What closedness is for: `fresh_location` is fresh for the whole state
and not only for the heap; an outcome is related to itself; and the
lemma on related states can extend a correspondence at an allocation.

**Valid values.** C3's invariant that a state holds valid values only
(`state_valid`) is extended to the fields of cells when the
primitives land (section 7.2); it is the same traversal as
`state_closed`, at another property.

**Names bound to nothing.** D8 makes "every symbol a term mentions is
bound" a conjunct of well-formedness, with its run invariant (C0's
follow-up); `state_closed` is the same for locations. The machine
does not rely on either: `exec_prim` has no value on an argument that
is a symbol or a location bound to nothing (section 2.5). The
invariants are for the theorem that a well-formed unit never reaches
such a use.

## 7. The fallout, and what the other changes mean for it

### 7.1 Measured on the prototype

**A new form of value, and the primitives under one constructor.**
Measured on the integration branch at 66bbc6b1be, file by file and
owner by owner, in `requests/C4-heap-fallout.md`: `Value_location`
with the types of the heap, the primitives under `Heap`, and the
repairs that they force, in nineteen files, most of them one more
name in a pattern. The types library is among them (four of its
files, T1's and T6's). No statement of an existing `Spec` file
changes.

**The primitives placed by arity**, as in the change and not in the
prototype: a case for each new constructor in each of the laws of
`eval_prim`, all trivial since `eval_prim` has no value on a
primitive of the heap. Not measured.

**The heap in the state** (D7). What follows in this section is an
old measurement, on 0a2933e7c9, before C2's kinds, C3's sets of
closures and the types; it has not been repeated, and its numbers are
not those of today. A plain search for applications of `State` finds
a third more on 1160b780f0 than it finds on 0a2933e7c9 (234 against
176, in 32 files against 18; the script finds a few more than the
search does). I wrote the script that adds the argument and ran it,
then stopped: what is left after it is binders and the names in
`intros`, by hand, in every proof that builds a state, and finishing
it would have shown nothing about the design. The counts, on
0a2933e7c9:

- 188 applications of `State` in 18 files; a script, not committed,
  adds the heap to each, named after the static environment beside
  it. `FlambdaSemanticsSpec.v`
  is right after it but for two lines.
- 69 statements, lemmas and auxiliary propositions in 12 files build a
  state and gain a binder for the heap (21 of them the step lemmas and
  congruence lemmas of `FlambdaSemanticsProofs.v`, 12 in
  `FlambdaContextProofs.v`, 9 in `FlambdaNormaliseProofs.v`). Most
  are lemmas of `Proofs` files: this is not a count of statements of
  `Spec` files. Like the 188, it is a textual count, not a compiled
  repair.
- `apply_cont_value`, `apply_continuation` and `call_function` build
  a state, so each gains the heap as an argument: 52 mentions in 11
  files.
- 184 lines of `intros` or `revert` in `Proofs` files name a static
  environment; that is the upper bound on the proof scripts to touch.
- `Exit` and `Exits`: 19 lines in 3 files, and one place in the test
  tool.

No statement changes meaning in that sweep: each is about one more
component that nothing reads. It is of the size of C2's first step
(the annotations), and like it is a replay for C0 once written.

### 7.2 What C2, C3, C5 and the types change for it

- **C2 (kinds), first.** A `Let` carries its kind and handlers and
  code a record of metadata: every `Let x d body` in the statements of
  section 4 gains the kind, and nothing else here changes. What I need
  from C2: its `state_well_kinded` takes the heap, and says that the
  fields of a cell are well-kinded values; its preservation theorem
  then needs, of `exec_prim`, the law that C1 gives it for
  `eval_prim` (the value of a primitive is of its result kind), which
  is one more law by cases. Neither is in the prototype, and both are
  owed at the epoch of the primitives. So is a third thing:
  `FlambdaPrimitiveSpec.prim_args_well_kinded`, by which C2's checker
  tests the kinds of the arguments of a primitive, is false on every
  primitive under `Heap` (they fall to its last case). The primitives
  of the heap must be given their cases there, and `exec_prim` the law
  that `eval_prim_kinds_statement` is for `eval_prim` (a primitive
  that has a value was given arguments of its kinds), or the checker
  refuses every program that allocates. The prototype is not affected
  (`eval_prim` has no value on a primitive of the heap, and the
  conversion makes none), and no new premise on kinds is asked of a
  term: the machine tests the kind where a cell is made or written.
- **C3 (closures of a set), first.** One more form of value and of
  static value. Rule 3 of the relation reads closures through
  `closure_in_set` in place of `closure_of` (same function slot, same
  code ids, related value slots); `locations_of_value`,
  `values_of_static` and the induction on values gain a case. C3 has
  since landed an invariant of states as well (`value_valid`,
  `allocated_valid`, `state_valid`: a well-formed unit holds valid
  values only). **It must reach the heap**, and that is owed by this
  design, with the primitives (epoch 2), not by C3: a location is
  valid as a value, and `state_valid` asks that every field of every
  cell be valid, the cells being one more place that the traversal
  of the values of a state visits (as for `state_closed`, section 6).
  Its preservation has two new cases: an allocation and a `Block_set`
  store valid values because their arguments are valid. In epoch 1
  the heap is carried and never written, so a heap that is valid stays
  valid, and a unit run from the empty heap has a valid one; nothing
  is claimed of an arbitrary heap that a state is given. It must not
  be left so when stores are turned on.
- **C5 (exceptions).** Its design, which is on the integration
  branch, adds no field to the state and does not change `Exit`: a
  raise is the `Apply_cont` it is. So the sweep of 7.1 is mine alone.
  `cont_value` has a form that holds values (`Extra_args`), so
  `cont_value_closed` and the action of a permutation gain a case.
  The prototype has met it: its machine follows `step` (a call
  evaluates the extra arguments of its exception continuation, and a
  continuation with extra arguments is applied to the arguments
  followed by them), and a continuation with extra arguments is one
  more case of what a continuation holds: in `cont_value_closed`, in
  the relation on continuations (two such are related when the
  continuations inside are and the extra arguments are), and in the
  invariant on the handlers that a continuation holds. The stack of
  handlers of C5's second machine (`FlambdaTrapSpec.v`) is not in
  `state`, so it adds nothing to the sweep. C5 needs nothing of
  the value raised, so matching on an exception, which is
  `Phys_equal` on an `Immutable_unique` block that Simplify has made
  static, can wait for symbols as addresses.
- **The types (T1, T2).** `type_satisfied` takes the heap beside the
  static environment, for `Mutable_block` and for `Variant` with
  `is_unique`, with the frame law
  `type_satisfied statics h vars v t -> heap_evolves h h' ->
  type_satisfied statics h' vars v t`, the twin of T1's law for a
  static environment that grows; T2 uses it where a handler runs
  later. T1 agrees, and has told me that its denotation will need a
  `Variant` type to hold of a mutable block, field by field (decision
  4): the first version is acceptable to T1 as a step only. The second
  stage of decision 4 gives that: `heap_evolves` then keeps the fields
  that are stable, so a `Variant` type may speak of a stable field of
  a mutable block.

## 8. The change, the statements that change meaning, and the epochs

### 8.1 The `Spec` diff, in its final shape

`FlambdaValueSpec.v` (as in the prototype):

```coq
Definition location : Type := positive.

 Inductive value : Type :=
   ...
+  | Value_location (l : location).

+Inductive cell : Type :=
+  | Cell_block (mut : cell_mutability) (tag : Z) (fields : list value).
+Definition heap : Type := list (location * cell).
+Definition empty_heap : heap := [].
+Definition cell_of (h : heap) (v : value) : option cell := ...
```

`FlambdaPrimitiveModel.v` (in the prototype these are under `Heap`):

```coq
+Inductive mutability : Type := Mutable | Immutable | Immutable_unique.
+Inductive init_or_assign : Type := Initialization | Assignment.
+Inductive equality_comparison : Type := Phys_eq | Phys_neq.

 Inductive unary_primitive : Type :=
-  | Block_load (kind : block_access_kind) (field : Z)
+  | Block_load (kind : block_access_kind) (mut : mutability) (field : Z)
   ...
 Inductive binary_primitive : Type :=
+  | Block_set (kind : block_access_kind) (init : init_or_assign) (field : Z)
+  | Phys_equal (op : equality_comparison)
   ...
 Inductive variadic_primitive : Type :=
-  | Make_block (kind : block_kind).
+  | Make_block (kind : block_kind) (mut : mutability).
```

A new file pair for what the primitives do to the heap (the
primitives' owner's, leaf work after the epoch): `fresh_location`,
`argument_bound`, `exec_prim`, `effects_of_prim`, `coeffects_of_prim`,
`heap_evolves`, the laws of 4.1 and the two of 2.5. In the prototype
they are in `FlambdaHeapSpec.v`. `Phys_equal` is in the primitives'
files before the heap, on immediates (P1).

`FlambdaSemanticsSpec.v`:

```coq
 Record state : Type := State {
   ...
-  state_statics : static_env
+  state_statics : static_env;
+  state_heap : heap
 }.

+Record outcome : Type := Outcome {
+  outcome_values : list value;
+  outcome_statics : static_env;
+  outcome_heap : heap
+}.

 Inductive step_result : Type :=
   | Step (s : state)
-  | Exit (k : continuation) (vs : list value)
+  | Exit (k : continuation) (o : outcome)
   | Undefined.

+Definition exec_named (statics : static_env) (h : heap) (vars : env)
+    (defining_expr : named) : option (value * heap) :=
+  match defining_expr with
+  | Prim p args =>
+    let* vs := eval_simples vars args in
+    exec_prim statics h p vs
+  | _ =>
+    let* v := eval_named statics vars defining_expr in
+    Some (v, h)
+  end.
```

`eval_named` stays, with every lemma about it. `step` is
`FlambdaHeapSpec.heap_step`: the old one with the heap carried, and
`exec_named` in the case of `Let`. `behaviour`, `refines`,
`equivalent`, `expr_refines` and `expr_equivalent` as in section 3.3.

A new file pair for the relation (C0's, core): `correspondence`,
`contents_related`, `value_step`, `value_related`,
`correspondence_valid`, `outcome_related`, `value_closed`,
`memory_closed`, `state_closed`. In the prototype they are in
`FlambdaHeapSpec.v`.

`FlambdaNormaliseSpec.v` (V1's): `prim_may_fold` becomes "no effects",
then "at most generative effects".

`FlambdaNominalSpec.v` (N1's): `unused_let_statement` gains a premise
on the effects of the defining expression (section 8.2).

### 8.2 Statements that change meaning

- **In the sweep (epoch 1): none.** Every statement quantifies over
  one more component and says the same of the rest.
  `heap_step_agrees_statement` (proved) is the reason: where the step
  is not a `Let` of a primitive, the machine with a heap steps as the
  machine without, and the heap is unchanged.
- **With the primitives (epoch 2).**
  - Every statement: the terms it is about now include those that
    allocate, read and write, and the values include locations.
  - `refines`, `equivalent`: an exit is compared by its values and its
    heap, both exactly; the static environment at exit is not
    compared, as today. This is stricter than section 3 and is sound;
    a rewrite that changes which allocations happen is not validated
    yet.
  - `remove_unused_lets_refines`: `prim_may_fold` is narrower. With
    today's definition the statement would be false: it would delete
    a `Block_set`.
  - `FlambdaNominalSpec.unused_let_statement`: **its text changes.**
    Today it is `~ var_free_in_expr x body -> expr_refines (Let x
    defining_expr body) body`, for every `defining_expr`. It gains
    the premise `named_has_no_effects defining_expr = true` (a
    `Simple`, a set of closures, a projection, or a primitive with
    `effects_of_prim p = No_effects`); in epoch 3 that becomes
    `named_at_most_generative_effects`. Both predicates are defined
    with `effects_of_prim` (in the prototype, `FlambdaHeapSpec.v`),
    as N1 asks: whether a binding may be erased is not a matter of
    names. Left as it is, the statement is false once `Block_set`
    exists (`delete_write_wrong`). R2's finding B2.
  - Of the three validators that erase bindings
    (`FlambdaNormaliseSpec.v`, extracted), only `remove_unused_lets`
    erases a primitive, through `named_may_go` and `prim_may_fold`:
    `named_may_go` becomes `named_has_no_effects`, then
    `named_at_most_generative_effects`. `remove_unused_total_lets`
    and `remove_unused_defined_lets` erase a `Simple` or a set of
    closures only and do not change.
  - `fold_constants_equivalent`: unchanged in text; a primitive of the
    heap applied to constants is not folded, since `eval_prim` has no
    value on it.
  - `drop_statics_refines`: its premise `envs_free_of` gains the heap
    (no cell refers to a name removed).
  - `validate_unit_sound`: from the empty heap; exits compared as
    above.
- **With the correspondence (epoch 3).**
  - `refines`, `equivalent`, and so every statement made with them:
    exits up to a correspondence; weaker than before on names of
    locations, on garbage and on a block against a symbol; the same on
    everything else.
  - `expr_refines`, `expr_equivalent`: over closed memories only.
    Weaker by a premise that every state reached from a term meets.
  - `refines_defined`, `refines_antisymmetric`: restated for the
    relation.
  - `plug_refines`, `plug_equivalent`: same text, new proof.
  - `validate_unit_sound`: as section 3.4 says.
  - Lifting on today's model (V3's `lift_unit`, when it is on the
    integration branch): the checked function gains a test, that the
    unit does not name a symbol that it lifts to, and
    `lift_unit_program_refines` is proved again for the relation
    (section 3.3). Without the test the theorem would be false of the
    new `refines`.
  So two things that exist would be false if epoch 2 left them as
  they are, and change with it: `prim_may_fold`, a definition, whose
  change keeps the text of `remove_unused_lets_refines`; and
  `unused_let_statement`, a statement, which gains a premise. The
  second version of this request said that no statement was
  falsified; that was wrong. I have looked for others by reading
  every statement of a `Spec` file that has a `Let` on one side only:
  the rest are about a `Simple` or a projection
  (`FlambdaControlFlowSpec.v`, `FlambdaStaticSpec.v`,
  `FlambdaNominalSpec.v:304-312`).

### 8.3 The epochs

0. **Before the heap: `Phys_equal` on immediates.** Leaf work in the
   primitives' files, under way (P1): the
   constructor, with a value on two tagged immediates and on an
   immediate against an allocated value. It is what lets programs
   with an integer `=` be checked (section 2.6).
1. **The heap in the state.** `state_heap`; `outcome` in `Exit`;
   `exec_named`, with `exec_prim` equal to `eval_prim` and the heap
   returned as it came; `Value_location`, `cell`, `heap` and `cell_of`;
   exits compared by values and heap. No new behaviour: no term makes
   a cell. C0 applies it with the script; the repairs are those of
   7.1. Review: the `Spec` diff is mechanical but for the five
   definitions above.
2. **Cells and primitives.** Leaf work, by the owner of the
   primitives' files or by me: the constructors of 8.1; `exec_prim` on
   them; the classification and its laws; `prim_may_fold`; the
   conversion in the test tool (refusing local modes, regions and
   static blocks that are not `Immutable`), the printing of an exit
   with its heap, and examples: a `ref` read and written; a record all
   of whose fields are mutable; `==` on two `ref`s; a write that
   Simplify must keep; the three terms of the discrepancies as
   examples that are reported as not checked or different. The CRs of
   decisions 3 to 5 go in with it.
3. **The correspondence.** On a branch first, as C2 did its repair:
   closedness and its preservation; transitivity; the lemma on related
   states; `plug_refines`; the lemma that carries over what exists.
   Transitivity, the lemma on related states and the invariant of
   closed states are proved in the prototype, for its copy of the
   machine and for the same expression on both sides (section 3.3); on the branch they are replayed in the
   real state and joined with today's lemma for related code.
   Then the epoch is a replay: `refines` and `expr_refines` change,
   `refines_exactly` keeps the old text, and no leaf file changes but
   by one line per theorem, with the two exceptions of section 3.3:
   the statements about static bindings that are dropped, and V3's
   lifting, whose checked function gains a test and whose theorem is
   proved again. After it, as leaf work: deleting an unused
   allocation (S5; proved in the prototype), lifting (S5, T6, with
   V3's relation), the instance of N1's interface.
4. **Small and separate, in any order after 3:** rule 5 (D26);
   symbols as addresses (static `Immutable_unique` and `Mutable`
   blocks; needed for exceptions that are matched); the second stage
   of decision 4, field stability (section 8.4), which is what brings
   records with both sorts of field in; arrays, bytes, float and
   mixed blocks, `Duplicate_block`.

Estimates. Epoch 1: a day for C0 with the script. Epoch 2: two days,
most of it the converter and the examples. Epoch 3: the proofs were
the cost, and those I was least sure of are done in the prototype
(2,200 lines for the relation's transitivity and the lemma on related
states, 600 for the invariant of closed states). What is left is
their replay in the real state, the join with related code and
`plug_refines`: some days of one agent, on a branch before the
epoch.

### 8.4 The second stage of decision 4, and what the compiler could say

**Field stability** (option (b) of decision 4). A cell remembers, for
each field, whether it is *stable*. The fields of an
`Immutable_unique` cell are stable from the allocation. A load marked
`Immutable` from a cell made `Mutable` has the value that the field
holds now, and makes the field stable. A `Block_set` of a stable field
has no value. Nothing else changes. This is the assumption of section
1.4 and no more: a field does not change after it has been read as
immutable. What it does to the design:

- `heap_evolves` keeps the contents of the stable fields (today: of
  the cells that are not mutable), and a stable field stays stable.
  A `Variant` type may then hold of a mutable block, about its stable
  fields, which is what T1 needs.
- The load marked `Immutable` changes the heap, by a mark. So two laws
  are restated: `no_effects` says that the heap after is the heap
  before with more fields stable; `no_coeffects` says that the value
  is the same in every heap that the heap *after* the load evolves
  to. `mutable_load_not_stable` is unchanged.
- The relation at exit orders the marks, as it orders poison: a cell
  of the target may have fewer stable fields than its counterpart,
  since Simplify deletes loads. In `outcome_equivalent` they are the
  same.
- A rewrite that adds an immutable load of a mutable block on a path
  where the source has none is not a refinement: the target could
  then go wrong at a later store. Simplify makes none: unboxing adds
  immutable loads to immutable blocks only (section 1.4).
- Covered: records with both sorts of field. Still undefined: a store
  after an immutable read of the same field (C4-2, R2-20), which is
  the assumption itself. Outside, by ruling: the blocks of
  tail-modulo-cons and the copy of a large record.
- Cost: a list of booleans in a cell, behind the observations of
  section 2.3; the two laws; one more ordering in the relation. No
  change to the compiler. Leaf work in the heap's files.

The second version of this request had a stricter rule under this
letter (a field both written and read as immutable made the later of
the two undefined), and said that it followed the compiler exactly.
It did not: it excluded a block that is filled and then read, as the
blocks of tail-modulo-cons are (R2's finding B3).

**Mutability by field** (option (c)). If `Make_block` said, for a
block made `Mutable`, which of its fields are mutable, a cell would
record it at allocation, a load marked `Immutable` would have a value
exactly on an immutable field, and nothing would be remembered about
reads. But a store into an immutable field must then be accounted
for. The copy of a large record stores into immutable fields with
`Assignment` (section 1.4, item 4; it is being fixed in production),
so the front end would have to mark such stores, `Duplicate_block`
would have to carry the mutabilities, and the model would need a
rule for when a field that is initialised becomes immutable: field
stability again, under another name. The compiler does not have the information in Flambda 2
today ("isn't currently propagated from `Lambda`", at
`Duplicate_block`; T1 tells me the types have a CR asking for
mutability by field in `Mutable_block`). As a production change it
is: the mutability of each field on `Pmakeblock`, which the front end
knows where it builds the record (`translcore.ml:2712`), carried by
`Make_block` and by `Duplicate_block`; and a mark on the stores of
`translcore.ml:2579-2605`. Its real benefit is for the types, which
could know the immutable fields of a mutable record from its
allocation on. The model does not need it to give such records a
meaning.

## 9. Trust

Enters the ledger's trusted OCaml, when the primitives land:

- the conversion of the new primitives and of the mutability of
  `Make_block` and `Block_load`, which must refuse and never
  approximate: a block kind or access kind other than `Values`, a
  static block that is not `Immutable`, a store marked
  `Initialization` (tail-modulo-cons) and `Duplicate_block` (the copy
  of a large record), both by ruling (decision 4), reported as not
  checked;
- one approximation, by decision (D37): region primitives are
  dropped and a local allocation, or an assignment with a local mode,
  is converted as one on the heap, with CRs in the conversion. It is
  trusted to be right for programs the type checker accepts;
- the printing of an exit, which now follows pointers into the heap.
  If the tool compares the two runs by what it prints, the numbering
  of locations in the print (in the order the exit values reach them)
  is trusted to be the same for two outcomes exactly when they are
  related. Better: `outcome_related` on finite memories is decidable,
  and a checker for it can be written in Rocq and proved against the
  relation, so that the tool compares with extracted code. Leaf work
  after epoch 3.

No axiom, no `Parameter`. `fresh_location` is extracted and is an
ordinary function.

## 10. What the prototype proves, and what it leaves

Proved, in `FlambdaHeapProofs.v` (`make -C rocq all` checks that each
statement of the `Spec` file is):

- the primitives: `fresh_location`; `exec_prim_symbols_bound`,
  `exec_prim_locations_bound`; `exec_prim_evolves`, `no_effects`,
  `only_generative_effects`, `no_coeffects`, `mutable_load_not_stable`;
- the machine: `heap_step_evolves`, `heap_step_agrees`;
- the relation at exit: `outcome_related_reflexive`,
  `outcome_equivalent_refines`, `outcome_equivalent_symmetric`,
  `outcome_related_transitive`, `related_projections`,
  `aliasing_observed`, `location_names_not_observed`,
  `block_and_symbol_related`, `boxed_poison_refined`,
  `garbage_not_observed`;
- the machine respects the relation: `heap_run_related`,
  `machine_respects_relation`, `closed_state_related`,
  `heap_refines_reflexive`;
- the invariant: `heap_step_closed`;
- the relation up to symbols that the second state binds:
  `states_related_nothing`, `heap_step_code_free_of`,
  `machine_respects_relation_except`;
- rewrites: `delete_unused_let`, `exchange_lets`, `cse_adjacent`,
  `load_known_field`, `lift_block`, `lift_closure`,
  `lift_closure_of_set`, and `delete_write_wrong`.

That is thirty-six. Nothing is stated and not proved.

Left:

- The heap is not in `state`: the prototype's machine is a copy. So
  no existing theorem has been re-proved with a heap, and the claim
  that each carries over rests on `heap_step_agrees` and on the
  counts of 7.1, not on a build.
- The prototype is on 66bbc6b1be. It has met C5's exceptions (section
  7.2), C2's kinds (its machine
  follows `step`: a `Let` carries a kind that is not looked at, and a
  call is undefined unless it agrees with the code called; each
  statement about a `Let` has its kind), C3's closures of a set
  (one more form of value: a case in the relation, which reads a
  closure as one of a set, in the induction on values and in
  `locations_of_value`) and C1's law on symbols bound to nothing
  (section 2.5 says what follows from that).
- The lemma on related states is for the relation without rule 5, and
  for states that run the same expression: related code, and
  `plug_refines`, are not done.
- Lifting is proved for a block and for closures. It is not stated
  for a boxed number, and no statement moves the `Let_static` to
  toplevel (section 4.2).
- Kinds and valid values do not reach the heap: C2's
  `state_well_kinded` and C3's `state_valid` do not visit cells, and
  `prim_args_well_kinded` is false on the primitives of the heap. All
  three are owed at the epoch of the primitives (section 7.2).
- Decision 4 is at its first stage: field stability (section 8.4) is
  not in the prototype.
- The primitives are under one constructor; `Block_load` with its
  mutability is two constructors (`Block_load` for the load marked
  `Immutable`, `Block_load_mutable`). `block_or_cell_of` is not
  defined.
- No conversion, no example in `tests/semantics/`: the test tool does
  not know the heap. The extracted files are regenerated and not
  committed.
- `make -s fmt` and `make -s test` were not run: no OCaml or dune file
  is changed.

## Decisions for the human

Each has the option the prototype takes meanwhile. A CR is the text
at the place in the `Spec` file where the model makes something
undefined without being forced to; the three are in
`FlambdaHeapSpec.v`, at the definitions.

1. **What has an identity** (section 2.1; D2). Recommendation: blocks
   made `Mutable` or `Immutable_unique`, and nothing else. Immutable
   blocks, boxed numbers and closures stay values. Prototype: so.
2. **What a location is** (2.2; D29). Recommendation: a name, with a
   fresh one chosen by a function of which only freshness is known.
   Prototype: so. N1 agrees.
3. **`Phys_equal`** (2.6; D19). Recommendation: option (b): defined
   but on two immutable allocated values. This is weaker coverage and
   not a faithful account: Simplify does decide some of those
   comparisons, and under (b) nothing is proved of a program from the
   first of them on. Prototype: so. The owner of the primitives
   agrees. On immediates it lands now, whatever is decided here. The
   CR, as it is in `FlambdaHeapSpec.v`:

       (* CR mshinwell: [Phys_equal] has no value on two immutable
          allocated values (blocks, boxed numbers, closures, strings).
          This is a limit of the model, not what the compiler does:
          the compiled comparison answers, and Simplify decides some
          of these (the same alias is equal, two different symbols are
          not: [Provers.prove_physical_equality]), while the sharing
          of immutable values ([Mutability.Immutable]; CSE of
          [Make_block] and [Box_number]; lifted constants) changes the
          answer that the machine would give. A program that makes
          such a comparison is undefined from there on, and the
          theorems do not cover it. Decision 3 of
          requests/C4-heap.md; discrepancies C4-3 and R2-21. *)

4. **A load marked `Immutable` from a block made `Mutable`** (1.4,
   8.4). In ordinary code this is the read of an immutable field of a
   record that also has a mutable field. Simplify assumes that a
   field does not change after it has been read as immutable; nothing
   checks it (C4-2, R2-20). Options:
   - (a) **No value.** Simple; and every record with both sorts of
     field is undefined from the first read of an immutable field, so
     the theorems say nothing of most real programs with records. T1:
     "the model would not be wrong, but it would not be about real
     programs. I do not think that can stay beyond a first version."
     This is a loss of coverage of ordinary source code, not a
     cautious reading of the compiler.
   - (b) **Field stability** (section 8.4). The load has the value
     that the field holds, and makes the field stable; a store into a
     stable field has no value. This is the compiler's assumption and
     no more. It needs no change to the compiler. Its costs: a cell
     remembers which of its fields are stable; `no_effects` and
     `no_coeffects` are restated; the relation at exit orders the
     marks.
   - (c) **Mutability by field, from the compiler** (section 8.4). A
     change to production code, whose benefit is for the types. It
     does not by itself account for stores into immutable fields, so
     it comes with new marks from the front end or with (b)'s rule.

   What each covers, by name (section 1.4 has the files and lines):

   | | (a) | (b) | (c) |
   |---|---|---|---|
   | a record with mutable and immutable fields | undefined at the first immutable read | covered | covered |
   | a store after an immutable read of the field (C4-2, R2-20) | undefined | undefined | undefined |
   | the blocks of tail-modulo-cons (R2-18) | out, by ruling | out, by ruling | out, by ruling |
   | the copy of a large record for `{ r with ... }`: `Duplicate_block`, then stores (C4-4) | out, by ruling | out, by ruling | out, by ruling |
   | recursive values (`caml_alloc_dummy`, `caml_update_dummy`) | out: calls of C functions; X5 found nothing wrong in them | the same | the same |
   | recursive modules (`CamlinternalMod.init_mod`, `update_mod`; X5-2, miscompiled) | out: calls into the run-time library, and a field may be read before it is overwritten | the same: no stage's rule holds of them | the same |

   **Ruled by the human, on tail-modulo-cons:** "we can ignore TMC
   for now b/c as you say the pass produces broken Lambda code, that
   needs fixing in the prod compiler."

   **Ruled by the human, on the copy of a record:** "I think we can
   not model Pduprecord for the moment, it is broken as you say and
   is being fixed in prod. I have a feeling that value_rec_compiler.ml
   may produce illegal lambda w.r.t. mutability as well".

   So both are outside what the design has to cover, at every stage,
   and by name: the conversion refuses a store marked `Initialization`
   (tail-modulo-cons is its only producer) and refuses
   `Duplicate_block`, and reports the unit as not checked. They are
   refused rather than left to whatever a stage of the model would
   say of them, so that neither comes in without anyone deciding to
   take it. (Were `Duplicate_block` modelled as a copy into a new
   mutable cell, field stability would give X5's program its meaning
   and the validation would fail on what Simplify makes of it, which
   is right. It is left out because the compiler is being fixed, not
   because the model could not say it.) Recursive values and
   recursive modules reach Flambda 2 as calls of functions outside
   the unit, which the model does not have, so a unit that has either
   is not checked. For recursive values that is the only reason: X5
   found nothing illegal in what `value_rec_compiler.ml` makes. For
   recursive modules there is a second one, which will remain when
   calls outside the unit are modelled: a field may be read as
   immutable before `update_mod` overwrites it, so field stability
   itself makes the overwrite undefined. They are outside what
   decision 4 covers at every stage, and X5-2 is the compiler's to
   fix.
   The note for the developers:

   > `lambda/tmc.ml` (:80, :156-168) allocates a constructor as
   > `Mutable` whatever its flag, fills one field later with
   > `Psetfield_computed (Pointer, Heap_initialization)`, and the block
   > is then read by loads marked immutable. Flambda 2 states no
   > contract under which a store into a field that is later read as
   > immutable is valid. The copy of a large record
   > (`translcore.ml:2553-2625`) has the same shape and is miscompiled.

   Recommendation: (a) as the stated restriction of the first stage
   (epochs 1 to 3), with the CR; then (b), as leaf work in the heap's
   files, before the corpus is real programs. (c) is for the
   compiler's developers to want, for the types; the model does not
   need it. The cell is kept behind observations (section 2.3) so
   that (b) changes the heap's files only. Prototype: (a). The CR, as
   it is in `FlambdaHeapSpec.v`:

       (* CR mshinwell: a [Block_load] marked [Immutable] has no value
          on a block made [Mutable]. Simplify takes a field so read
          never to change afterwards (it records the field in the type
          of the block and shares later loads), and nothing checks
          that (C4-2, R2-20). This first stage excludes more than that
          assumption does: every record with both mutable and
          immutable fields, from the first read of an immutable field.
          Two things that the front end makes are outside the model by
          ruling, at every stage, and the conversion refuses them:
          - the blocks that tail-modulo-cons builds (lambda/tmc.ml:
            placeholders made [Mutable], filled with
            [Heap_initialization], then read with immutable loads;
            R2-18): "we can ignore TMC for now b/c ... the pass
            produces broken Lambda code, that needs fixing in the prod
            compiler";
          - [Duplicate_block] followed by stores, which is the copy of
            a large record for [{ r with ... }] (lambda/translcore.ml,
            [transl_record]; miscompiled today, C4-4): "I think we can
            not model Pduprecord for the moment, it is broken as you
            say and is being fixed in prod".
          Decision 4 of requests/C4-heap.md. *)

5. **`Block_set` into what was not made `Mutable`**: an immutable
   block, a static block, an `Immutable_unique` cell. Recommendation:
   no value. The front end makes no such store: every store of
   `lambda/` is into a record with a mutable field, a `ref`, an
   object, a copy made by `Pduprecord` or a placeholder of
   tail-modulo-cons, and all of those are `Mutable` (section 1.4).
   **A store marked `Initialization`** is made by tail-modulo-cons
   only, and reaches Flambda 2 as an `Array_set`: no `Block_set` from
   source carries the mark. The machine does not look at the mark,
   and the conversion refuses it (decision 4). With the second stage
   of decision 4, a store into a stable field has no value either.
   Prototype: so. The CR, as it is in `FlambdaHeapSpec.v`:

       (* CR mshinwell: [Block_set] has no value on a block that was
          not made [Mutable]: an immutable block, a symbol, an
          [Immutable_unique] cell. The machine would write; Simplify
          keeps the facts it has about the block. The front end makes
          no such store: every store of lambda/ is into a record with
          a mutable field, a [ref], an object, a copy made by
          [Pduprecord] or a placeholder of tail-modulo-cons. [init]
          does not change what the store does; the only stores marked
          [Initialization] are those of tail-modulo-cons, which the
          conversion refuses (decision 4). Decision 5 of
          requests/C4-heap.md. *)

6. **What an exit observes** (section 3; D6, D26; changes what
   `validate_unit_sound` says). Options, cumulative: (i) values and
   the heap as they are; (ii) up to a bijection on locations, on what
   the values reach; (iii) and immutable values by contents, through
   symbols (D6); (iv) and a poison of the source may be anything of
   its kind in the target, inside a boxed number too (D26).
   Recommendation: (i) for epoch 2; (ii) and (iii) together in epoch
   3; (iv) after, as a separate small change, since it makes two
   relations of one. Prototype: the relation has (ii) to (iv), with
   (iv) behind a flag, and composes with the flag either way.
7. **Closures at exit** (D1). Recommendation: unchanged, the whole
   value; the correspondence has room for S4's relation on code ids.
8. **How the heap enters the statements** (D7). Options: (a) a fifth
   field of the state, named by every statement that builds one: the
   sweep of 7.1; (b) the static environment and the heap under one
   field, a record of the memory, so that a later addition to the
   memory touches no statement. Under (b) every function that takes
   the static environment (`closure_of`, `eval_prim`, the
   observations, about 200 lines that mention it) takes the record or
   a projection of it, which is more to change now than (a), and
   nothing planned adds to the memory: C5's recommended design adds no
   field at all. Recommendation: (a).
9. **`expr_refines` over closed memories only.** Needed for the lemma
   on related states; holds of every state reached from a term.
   Recommendation: yes, in the definition. Prototype: so
   (`heap_expr_refines`).
10. **Scope** (1.5): local allocation and regions not modelled (the
    conversion drops regions and reads a local allocation as one on
    the heap, D37); arrays, bytes,
    float and mixed blocks, `Duplicate_array` and `Obj_dup` later as
    leaf work; `Duplicate_block` out by ruling (decision 4) until the
    compiler is fixed; atomics,
    bigarrays, lazy blocks and off-heap memory out; static blocks that
    are not `Immutable` out until symbols are addresses.
    Recommendation: as listed.
11. **A load marked `Mutable` from an immutable block.**
    Recommendation: defined, as C1's load (the mark is a licence for
    the compiler, not a test). Nothing is undefined, so no CR. It
    arises where `%field0` or `%field1`, which are read with
    `Reads_vary`, is applied to an immutable block by an external
    that a program declares for itself (V2's probe). The standard
    library's `fst` and `snd` are `%field0_immut` and `%field1_immut`
    (`stdlib/stdlib.ml:245-246`), an immutable load, and `!` is a
    mutable load from a mutable block. Prototype: so
    (`Block_load_mutable` on a value that is not a location is
    `eval_block_load`).
12. **A primitive applied to a location that is not bound** has no
    value. This is D8 for locations, and no state reached from a term
    has such a location; I take it as ruled and put no CR. Prototype:
    so, for every primitive and every argument, symbols bound to
    nothing included (section 2.5).

## Discrepancies recorded

In the team's record of discrepancies. The first three each have an
fexpr term that was given to the real Simplify (not compiled and run):

- C4-1: an `Immutable_unique` block with constant fields is lifted
  from inside a function to one symbol. A function that returns such
  a block, called twice: the two results are different blocks before
  Simplify and the same symbol after.
- C4-2: nothing checks that a field loaded as immutable is never
  written. A load marked `Immutable`, a `Block_set` of the same field,
  the same load again: Simplify replaces the second load by the first.
- C4-3: the comment that physical equality is referential on immutable
  blocks, against CSE and sharing. `Phys_equal` of two equal
  `Make_block`s is folded to true.
- C4-4: the copy of a large record for `{ r with ... }` stores, with
  `Assignment`, into fields that are immutable by type and are read
  as immutable afterwards. Found by reading; X5 then showed that it
  is miscompiled, from OCaml source with the default flags: the copy
  is given the type of the original, and a read after the store
  returns the old value (`record_update.ml`, with X5's series).

R2's, on the same matters: R2-18
(tail-modulo-cons), R2-19 (C4-1 again, with the function's own
region), R2-20 (C4-2 again), R2-21 (C4-3 again, and two symbols with
equal contents proved different).

## Not read

- `to_cmm/` beyond `phys_equal` and where placement and validity are
  used.
- `simplify/flow/mutable_unboxing.ml` (out of scope by the plan).
- `common_subexpression_elimination.ml` and `join_points.ml` (CSE
  across a join).
- The typing of records and of `let rec` (`typing/`), on which the
  claims of section 1.4 about which fields a program may store into
  rest: I read what `lambda/` does with the labels it is given.
- `CamlinternalOO` and the runtime's allocation of objects.
- C5's request, which is not written; what is said of C5 here is from
  its owner's message.
