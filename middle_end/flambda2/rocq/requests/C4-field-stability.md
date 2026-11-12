# C4, the heap: a record with fields of both kinds (a question)

One page, for the human. It is decision 4 of `requests/C4-heap.md`
again, now with figures. Nothing here is applied; no Rocq changes.

## The fact

`type t = { name : int; mutable count : int }`. The front end makes a
value of this type one block, made `Mutable`. A read of `count` is a
`Block_load` marked `Mutable`. A read of `name` is a `Block_load`
marked `Immutable`, of a block that was made `Mutable`.

Simplify treats a load marked `Immutable` as final: it records the
field in the type of the block, replaces a later load of the same
field by the first, and keeps what it knows of the field across
stores and calls. Nothing in the compiler checks that no store into
that field follows (C4-2 and R2-20 in `DECISIONS.md`).

## The model as it is: the first stage

A load marked `Immutable` has no value on a block made `Mutable`
(`FlambdaHeapSpec.load_allowed`). It has one on a block made
`Immutable_unique`, which nothing writes. So a unit with such a record
is undefined, before Simplify and after it, from its first read of an
immutable field. That is sound, and it is a loss of coverage: the
tool is to answer "undefined" of every such unit, never "validated".

Measured by T5 on 216 units with mutable state, each run for real
four times and each term run by the heap's machine of the prototype
(T5's units and its table are not in this tree): 158 run on both
terms and return what the real run returns; 21 are undefined for
this reason alone, which is every unit that has a record with fields
of both kinds and reads an immutable field of it (five more have such
a record and never read the immutable field); 1 is undefined for
`Phys_equal` of two immutable allocated values; 36 are not run
(copies of array literals, the empty array, floats, C calls). The
smallest of the 21 makes a record and reads its immutable field;
nothing ever writes the record. In a variant of the machine in which
`load_allowed` always answers yes, which is not the model, all 21
return what the real run returns, on both terms.

## The rule proposed: field stability, the second stage

- A block made `Mutable` remembers which of its fields a load marked
  `Immutable` has read: those fields are stable.
- A `Block_load` of a block reads the field as it is now, whatever its
  mark. One marked `Immutable` (or `Immutable_unique`) leaves the
  field stable. One marked `Mutable` reads a stable field too, and
  changes nothing.
- A `Block_set` into a stable field has no value: the run is
  undefined from there, whatever is stored, the value that the field
  already holds included. A store into another field of the same
  block is as before.

So the rule is: no store into a field after it has been read as
immutable. It is what Simplify assumes, said as a rule of the machine
instead of a property of the front end: a program that breaks it is
undefined in the model, and Simplify may do anything to it. It needs
no change to the compiler. It is written and proved over the
prototype of the heap, arrays included, in a rehearsal that is not in
this tree (forty-five statements; R5 has read them).

## What each choice does to the sharing of loads

- **The first stage, kept.** Sharing two loads marked `Immutable` is
  sound, because the only cells they read are never written. Every
  record with fields of both kinds stays outside the model.
- **Field stability.** Sharing two loads marked `Immutable` of one
  field of one block is sound across anything between them: the first
  makes the field stable, and a store between the two is undefined,
  so the term before goes wrong and any term refines it. A load
  marked `Mutable` is not shared across a store or a call, as today.
  The cost: such a load now changes the heap (it marks the field), so
  the laws "no effects" and "no coeffects" are said up to the marks
  (done in the rehearsal), and two exits cannot be compared with
  their marks: a term after in which Simplify shared or removed a
  load marks fewer fields. The comparison of exits must leave the
  marks out, or order them. That is why R5 advised that this stage
  land with the comparison of exits up to a correspondence, or after
  it. With the comparison cell by cell that the passes changing
  values now need, leaving the marks out is one clause more.
- **The mutability of each field, from the compiler.** If
  `Make_block` said which fields may be written, a load would mark
  nothing and a store into a field not so declared would be undefined
  at the store. Simpler in the model, and a change to the compiler's
  terms, which this work does not make.

## The question

1. Is field stability the meaning wanted for a load marked
   `Immutable` of a block made `Mutable`, or should the model wait
   for the mutability of each field from the compiler, or stay at the
   first stage?
2. If field stability: with the primitives of the heap on `step`
   (then the 21 units run at the first tool that converts a store,
   and the comparison of exits leaves the marks out from the start),
   or after the comparison up to a correspondence, as R5 advised?
