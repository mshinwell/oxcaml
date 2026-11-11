# Trust ledger of the Rocq developments

What the theorems rest on that no proof covers: every axiom, and every
piece of OCaml that is trusted. Each has its reason. A `Parameter` is an
axiom too: it assumes that something of its type exists.

The first part of each section is checked. `make -C rocq assumptions`
fails if

- Rocq reports an axiom that this file does not list, or this file lists
  one that Rocq no longer reports (the report is the one of `rocq check`
  on every module of `rocq/Makefile`, printed under "Global assumptions");
- a statement of a Spec file of the Flambda 2 libraries depends on an
  axiom that is not in the section "Flambda 2" below (`Print Assumptions`
  on each theorem that `make claims` checks).

The trusted OCaml cannot be checked by a tool. It is listed for the
reviewers, who read it against the compiler.

The rules, for the Flambda 2 work (`middle_end/flambda2/rocq/`
`PARALLEL-PLAN.md`, sections 4, 5 and 7):

- Nothing is `Admitted`, and there is no axiom that is not here.
- No workstream adds to this file without a reviewer's sign-off. The
  reviewers (R1, R2) own it.
- It should shrink. Each entry of the Flambda 2 section says what would
  remove it.

The format, which the check relies on: an axiom is a list item that
begins with its fully qualified name between backquotes, and nothing else
begins so. The second check takes the Flambda 2 axioms to be those
between the heading "Flambda 2" and the next heading of its level.

## Flambda 2

The libraries `OxCamlFlambda2` (`middle_end/flambda2/rocq/`) and
`OxCamlFlambda2Types` (`middle_end/flambda2/types/rocq/`).

### Axioms

None. No statement of these libraries depends on an axiom: none uses
classical logic, Rocq's primitive integers or the models of OxCaml's
types below. (There were seven, all about the primitives, which the model
left abstract. The primitives are now data,
`middle_end/flambda2/rocq/FlambdaPrimitiveModel.v`, and what they compute
is a definition, `FlambdaPrimitiveSpec.v`.)

### Trusted OCaml

None of this is used by a proof. It is what connects the proofs to the
compiler in the tests of `middle_end/flambda2/tests/semantics/`: when the
tool reports a pair of terms as validated, the theorem
(`FlambdaValidateSpec.validate_unit_sound`) is about the two model terms,
and what follows is why they stand for what Simplify was given and what
it gave back.

- **The conversion of terms**, in
  `middle_end/flambda2/tests/tools/flsemantics.ml` (`convert_expr` and
  the functions around it, about 230 lines): from the compiler's Flambda
  terms to the terms of `FlambdaModel.v`. It is trusted to give a term
  with the meaning of the one it is given, and to refuse (`Unsupported`)
  what the model has not got, never to approximate it. To be read case by
  case against `terms/`. Workstream V3 owns it and is to add a printer
  back to fexpr and round-trip tests.
- **The conversion of primitives**, in the same file (the section
  "Primitives"): one function for each arity of primitive that the model
  has (`convert_unary_primitive`, `convert_binary_primitive` and, once
  the model has `Make_block`, `convert_variadic_primitive`), with the
  conversions of what a primitive carries (`convert_kind`,
  `convert_standard_int`, the signedness, the operations and the
  comparisons; later `convert_boxable_number` and `convert_or_unknown`).
  It is about 95 lines with the primitives of the first stage and 145
  with those of the third. It says which primitive of
  `FlambdaPrimitiveModel.v` stands for one of the compiler's. It is a
  renaming of constructors, with the fields the model keeps. Trusted:
  that it sends a primitive to the one of the same name, and refuses a
  primitive, or a value of a field, that the model has not got. Of the
  primitives that allocate or load, that is: an allocation that is not
  on the heap; a block that is not immutable or not of values; and, for
  `Make_block`, a kind of a field that says more than `any_value`, as
  the model has no subkinds and Simplify uses them. What a primitive
  computes is not here: it is `FlambdaPrimitiveSpec.eval_prim`, to be
  read against `terms/flambda_primitive.mli` and
  `simplify/simplify_*_primitive.ml`.
- **The conversion of numeric constants**, in the same file (the section
  "Numbers", `convert_const`, `convert_float32`, `convert_float` and the
  boxed numbers of `convert_static_const`, about 100 lines): from the
  compiler's integers of each width, and the bit patterns of its floats,
  to the integer that a constant of the model carries. Trusted: that each
  number is converted to itself, at every width and at its bounds. (It
  was not so: until this conversion went through `int64`, `z_of_int`
  converted the least tagged or naked immediate to -1, and what the tool
  reported before then is not made good by the repair.) Constants of the
  vector and mask kinds, and poison, are refused, so the tool does not
  exercise what the model says of boxing and unboxing at those kinds.
- **The numbering of names**, in the same file (`Numbering`, about 30
  lines): each variable, continuation, symbol, code id and value slot of
  the compiler gets a number, the same throughout a unit. Trusted: that
  the compiler's names are fresh, so that one name stands for one thing.
- **The identification of names across the two terms**, in the same
  file (`convert_both` with `code_id_used`, about 70 lines). The two
  units are converted with one numbering, the return and exception
  continuations of the unit after standing for those of the unit before.
  And Simplify gives a new code id to each new version of code: the tool
  gives the new id the number of the old one where the old one is bound
  as deleted and not otherwise used. Trusted: that this identifies only
  what is the same continuation and the same function. The second part
  goes when the comparison relates code ids itself (workstream S4; there
  are notes in `flsemantics.ml` and `FlambdaCompareSpec.v`).
- **The extraction**: Rocq's extraction to OCaml, by
  `middle_end/flambda2/rocq/FlambdaExtract.v`. It has no directive that
  realises a definition of the model by hand-written OCaml. The extracted
  modules are in `middle_end/flambda2/tests/semantics/extracted/`.
- **What the tool reports**, in the same file (`check`, `run`,
  `observe`): that it calls `validate_unit` on the two terms converted,
  and prints its answer as it is. The comparison of the two runs that it
  also prints is a test of one run, and no theorem is about it.

Not trusted, though it is OCaml: which static bindings the tool proposes
to remove as unused (`unused_statics`). The extracted `drop_statics`
checks the proposal, and `validate_unit_sound` holds whatever it is.

## The SSA loop passes

The libraries `OxCamlStdlib` (`rocq/`), `OxCamlBackend` (`backend/rocq/`),
`OxCamlSsa` (`backend/ssa/rocq/`) and `OxCamlLoop`
(`backend/ssa/loop/rocq/`). `ROCQ-REVIEW-GUIDE.md` (sections 2.3 and 2.4)
says what each group is to be checked against; the reasons here are
short. The trusted OCaml of these libraries is the extraction directives
of their `*Extract.v` files and the hand-written rewrites of the passes,
which that guide covers (sections 2.3, 4.7 and 5.5).

### `Int64` (`rocq/OxCamlInt64.v`)

Rocq has no 64-bit machine integer. `Int64` is an abstract type with its
operations, and each axiom is the documented behaviour of one OxCaml
operation; `int32`, `int64` and `nativeint` are the types of constants
the models carry and do not compute with.

- `OxCamlStdlib.OxCamlInt64.Int64.abs_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.add_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.compare_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.div_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.equal_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.mul_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.neg_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.of_int_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.rem_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.shift_right_logical_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.shift_right_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.sub_spec`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_bounded`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_max_int`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_min_int`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_minus_one`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_one`
- `OxCamlStdlib.OxCamlInt64.Int64.to_Z_zero`
- `OxCamlStdlib.OxCamlInt64.Int64.to_int_exact`
- `OxCamlStdlib.OxCamlInt64.int32`
- `OxCamlStdlib.OxCamlInt64.int64`
- `OxCamlStdlib.OxCamlInt64.int64_abs`
- `OxCamlStdlib.OxCamlInt64.int64_add`
- `OxCamlStdlib.OxCamlInt64.int64_compare`
- `OxCamlStdlib.OxCamlInt64.int64_div`
- `OxCamlStdlib.OxCamlInt64.int64_equal`
- `OxCamlStdlib.OxCamlInt64.int64_max_int`
- `OxCamlStdlib.OxCamlInt64.int64_min_int`
- `OxCamlStdlib.OxCamlInt64.int64_minus_one`
- `OxCamlStdlib.OxCamlInt64.int64_mul`
- `OxCamlStdlib.OxCamlInt64.int64_neg`
- `OxCamlStdlib.OxCamlInt64.int64_of_int`
- `OxCamlStdlib.OxCamlInt64.int64_one`
- `OxCamlStdlib.OxCamlInt64.int64_rem`
- `OxCamlStdlib.OxCamlInt64.int64_shift_right`
- `OxCamlStdlib.OxCamlInt64.int64_shift_right_logical`
- `OxCamlStdlib.OxCamlInt64.int64_sub`
- `OxCamlStdlib.OxCamlInt64.int64_to_Z`
- `OxCamlStdlib.OxCamlInt64.int64_to_int`
- `OxCamlStdlib.OxCamlInt64.int64_zero`
- `OxCamlStdlib.OxCamlInt64.nativeint`
- `OxCamlStdlib.OxCamlInt64.nativeint_to_int64`

### Overflow tests (`rocq/IntArith.v`)

Four tests of whether a sum or a product fits its type, each a few lines
of OCaml in `rocq/IntArithExtract.v` that are easier to read than to
model, with an axiom saying that it answers the question.

- `OxCamlStdlib.IntArith.add_fits`
- `OxCamlStdlib.IntArith.add_fits64`
- `OxCamlStdlib.IntArith.add_fits64_spec`
- `OxCamlStdlib.IntArith.add_fits_spec`
- `OxCamlStdlib.IntArith.mul_fits`
- `OxCamlStdlib.IntArith.mul_fits64`
- `OxCamlStdlib.IntArith.mul_fits64_spec`
- `OxCamlStdlib.IntArith.mul_fits_spec`

### List functions (`rocq/OxCamlList.v`)

Two functions of OxCaml's `List` that are mapped onto OxCaml's own
instead of being extracted, with what the models use of them.

- `OxCamlStdlib.OxCamlList.compare_length_with`
- `OxCamlStdlib.OxCamlList.sort_uniq`
- `OxCamlStdlib.OxCamlList.sort_uniq_In`
- `OxCamlStdlib.OxCamlList.sort_uniq_NoDup`

### Operations of the backend (`backend/rocq/Operation.v`)

The payloads of `Operation.t` that no model looks inside are abstract
types. `specific_linear` is the target's reading of its specific
operations as linear combinations of their arguments, the one thing
taken on trust about a target's semantics.

- `OxCamlBackend.Operation.addressing_mode`
- `OxCamlBackend.Operation.alloc`
- `OxCamlBackend.Operation.float_operation`
- `OxCamlBackend.Operation.float_width`
- `OxCamlBackend.Operation.int128_operation`
- `OxCamlBackend.Operation.intop_atomic`
- `OxCamlBackend.Operation.load`
- `OxCamlBackend.Operation.memory_chunk`
- `OxCamlBackend.Operation.name_for_debugger`
- `OxCamlBackend.Operation.probe_is_enabled`
- `OxCamlBackend.Operation.reinterpret_cast`
- `OxCamlBackend.Operation.signedness`
- `OxCamlBackend.Operation.specific_linear`
- `OxCamlBackend.Operation.specific_operation`
- `OxCamlBackend.Operation.static_cast`
- `OxCamlBackend.Operation.symbol`
- `OxCamlBackend.Operation.test`
- `OxCamlBackend.Operation.vec128_bits`
- `OxCamlBackend.Operation.vec256_bits`
- `OxCamlBackend.Operation.vec512_bits`

### The SSA graph (`backend/ssa/rocq/SsaModel.v`)

Blocks, instruction identifiers and sets of blocks are the compiler's
own data, abstract in the models: the types, the observations the models
make of a block, equality tests with the axioms that they decide
identity, and sets with the axioms of membership.

- `OxCamlSsa.SsaModel.all_successors`
- `OxCamlSsa.SsaModel.block`
- `OxCamlSsa.SsaModel.block_body`
- `OxCamlSsa.SsaModel.block_eqb`
- `OxCamlSsa.SsaModel.block_eqb_spec`
- `OxCamlSsa.SsaModel.blockset`
- `OxCamlSsa.SsaModel.dominates`
- `OxCamlSsa.SsaModel.instr_id`
- `OxCamlSsa.SsaModel.instr_id_eqb`
- `OxCamlSsa.SsaModel.instr_id_eqb_spec`
- `OxCamlSsa.SsaModel.op_def`
- `OxCamlSsa.SsaModel.op_def_find`
- `OxCamlSsa.SsaModel.param`
- `OxCamlSsa.SsaModel.params`
- `OxCamlSsa.SsaModel.predecessors`
- `OxCamlSsa.SsaModel.raise_kind`
- `OxCamlSsa.SsaModel.set_add`
- `OxCamlSsa.SsaModel.set_empty`
- `OxCamlSsa.SsaModel.set_for_all`
- `OxCamlSsa.SsaModel.set_for_all_spec`
- `OxCamlSsa.SsaModel.set_mem`
- `OxCamlSsa.SsaModel.set_mem_add`
- `OxCamlSsa.SsaModel.set_mem_empty`
- `OxCamlSsa.SsaModel.set_mem_singleton`
- `OxCamlSsa.SsaModel.set_singleton`
- `OxCamlSsa.SsaModel.strict_dominators`
- `OxCamlSsa.SsaModel.terminator`
- `OxCamlSsa.SsaModel.value_eqb`
- `OxCamlSsa.SsaModel.value_eqb_spec`

## Rocq's own

### Primitive 63-bit integers

Rocq's `int` is OxCaml's `int`. Its operations are primitives of Rocq's
kernel, and their specifications are axioms of Rocq's library. Only the
SSA libraries use them.

- `Corelib.Numbers.Cyclic.Int63.PrimInt63.add`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.addc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.addcarryc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.addmuldiv`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.asr`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.compare`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.compares`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.div`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.diveucl_21`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.divs`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.head0`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.int`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.land`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.leb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lor`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mod`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mods`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mul`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.sub`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.subc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.subcarryc`
- `Corelib.Numbers.Cyclic.Int63.PrimInt63.tail0`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.asr_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.compare_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.div_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.leb_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.ltb_spec`
- `Corelib.Numbers.Cyclic.Int63.Sint63Axioms.mod_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.add_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.addc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.addcarryc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.addmuldiv_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.compare_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.div_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.diveucl_21_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.diveucl_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_correct`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.eqb_refl`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.head0_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.land_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.leb_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lor_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lsl_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lsr_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.ltb_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.lxor_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.mod_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.mul_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.mulc_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.of_to_Z`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.sub_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.subc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.subcarryc_def_spec`
- `Corelib.Numbers.Cyclic.Int63.Uint63Axioms.tail0_spec`

### Classical logic

The excluded middle, used by the SSA libraries for case splits on whether
a register is defined. No statement of the Flambda 2 libraries uses it,
and the second check above keeps it so.

- `Stdlib.Logic.Classical_Prop.classic`
