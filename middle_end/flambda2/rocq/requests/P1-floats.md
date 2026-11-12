# P1: floating-point arithmetic in the model. A request

Owner: P1. For the human. Nothing here is done: this says what the
model would need for floats and what each way of getting it costs.
For what a NaN is it gives two options and does not choose. Four of
V2's units stop on floats today (`float_add.ml` and two like it on
`+.`, one on `float_of_int`).

## What there is

A float constant of the model is its bit pattern, an integer
(`Naked_float`, `Naked_float32`, FlambdaValueSpec.v), in range by
`const_in_range`. Boxing and unboxing of floats are there. No
primitive computes on one: the conversion refuses `Float_arith`,
`Float_comp` and `Num_conv` to or from a float.

## What Simplify does with floats

- It folds, on constants, the binary `Float_arith` (`Add`, `Sub`,
  `Mul`, `Div`), the unary one (`Abs`, `Neg`), `Float_comp` and the
  conversions, unless `-no-float-const-prop` is given
  (`DE.propagating_float_consts`; `simplify_binary_primitive.ml`,
  `simplify_unary_primitive.ml`).
- It computes with the floats of the machine the compiler runs on
  (`Numeric_types.Float_by_bit_pattern.IEEE_semantics`: `Stdlib.( +. )`
  and the like; C stubs for `float32`), and keeps results as bit
  patterns, so +0 and -0 differ and so do two NaNs.
- Where one argument is known it applies only identities that it takes
  to keep the bit pattern: `x *. 1.`, `1. *. x` and `x /. 1.` are `x`;
  `x *. -1.`, `-1. *. x` and `x /. -1.` are `Neg x`. It has none for
  `+.` (its comment: `x +. 0.` is not `x` when `x` is -0) and none for
  `-.`.
- A comparison with a constant NaN is folded (`Neq` true, the others
  false); `compare` on floats is the total order of `Stdlib.compare`.

Three places where the machine may not agree with it, recorded as
P1-6, P1-7 and P1-8, and tried on the compiler built from this tree,
on x86-64 for x86-64:
1. (P1-8) Which NaN a folded operation returns is the host's. x86-64
   gives the negative quiet NaN for `0. /. 0.`, arm64 the positive
   one; for two NaN operands the result depends on the order the
   backend gives the instruction its operands. Tried and not
   reproduced: where the host is the target, the folded and the
   computed results agree on the cases tried. Open for a compiler
   that runs on one and compiles for the other.
2. (P1-6) `x *. 1.` of a signalling NaN is that NaN made quiet on the
   machine, and `x` in Simplify. Shown: the bits that a program
   prints differ according to whether Simplify sees the 1.
3. (P1-7) `x *. -1.` of a NaN keeps its sign on the machine, and
   `Neg x` flips it. Shown, in the same way.
Simplify's comment says that its identities on floats keep the bit
pattern; on a NaN these two do not. That is all that is shown: no
wrong result for a program that does not read the bits of a NaN, and
whether it is a bug is for the compiler's developers.

## What the model needs

1. Operations on bit patterns: decode to sign, exponent and mantissa,
   compute with rounding to nearest even, encode; at 64 and at 32
   bits. +0 and -0 are two bit patterns and stay two values: only a
   comparison reads them as equal.
   `Abs` and `Neg` are not arithmetic: they clear or flip the sign bit
   and keep every other bit, on a NaN as on any float, as the machine
   and Simplify do. Point 4 is not about them: `Neg` of a NaN is
   that NaN with the other sign.
2. Comparison with NaN unordered, and the total order for `compare`.
3. Conversions: integer to float (rounded), float to integer
   (truncated), between the two widths.
4. What arithmetic returns on a NaN (below: two options).
5. A rule for a conversion to an integer of a NaN or of a float out of
   range: OCaml leaves it unspecified and x86-64 and arm64 differ. I
   would make it undefined, with a CR. That is a part of the language
   left out of the model on purpose, to be said at the definition and
   ruled on; it is not there to make a proof go through.

## Where the arithmetic would come from

| Source | Has | Adds to the trust ledger |
|--------|-----|--------------------------|
| `Corelib.Floats.SpecFloat` (in the installed Rocq) | IEEE 754 in Rocq on integers, any precision, so 64 and 32 bits; one NaN, no payload; `SFadd`, `SFmul`, `SFdiv`, `SFcompare`, rounding to nearest even | Nothing: definitions only. It is the specification one reads. About 80 lines of ours for bit patterns and conversions |
| `PrimFloat` (the kernel's machine floats) | 64 bits only; fast; one NaN | To prove anything, the 22 axioms of `FloatAxioms.v`. To run, the extraction to OCaml's floats, that is the host's, as Simplify uses: the test would compare the host with itself |
| Flocq (not installed) | 64 and 32 bits, NaN payloads, the rule for NaN as a parameter, proofs against the reals; what CompCert uses, with a rule per target | A new dependency of `make -C rocq`; proofs through it use the axioms of Rocq's reals |

## What a NaN is in the model: two options, and no choice made here

The machine of the model is a function, and which NaN the hardware
returns is not fixed by the term. Simplify has identities that do not
keep the bits of a NaN (P1-6, P1-7), under a comment that says they
keep the bit pattern. So what the model says of a NaN decides whether
those identities are right. That is a statement about OCaml and not
about the model, and it is not chosen here.

CR mshinwell: which of the two options below. Under the first, P1-6
and P1-7 are mistakes of Simplify, and its comment is right. Under
the second, the identities are right and the comment says too much.

**Option 1: the bit pattern of a NaN is kept.** A float is its bits,
a NaN included, and nothing is compared up to anything.
- What `eval_prim` returns on a NaN: a definite bit pattern, by the
  rule of one target, as CompCert has a rule per target. On x86-64: a
  NaN operand is returned, made quiet, the first if both are NaNs;
  an invalid operation on numbers (`0. /. 0.`) gives the negative
  quiet NaN (seen in the runs of P1-6 to P1-8). arm64 differs, by its
  manual, which was not tried: the positive one, and its own order
  between two NaNs. `Abs` and `Neg` change the sign bit only.
- Which identities survive: none of `x *. 1.`, `1. *. x`, `x /. 1.`
  (wrong on a signalling NaN) and `x *. -1.`, `-1. *. x`, `x /. -1.`
  (wrong on every NaN), unless `x` is known not to be a NaN, which
  Simplify can seldom prove. A unit in which Simplify applies one to
  an unknown `x` is then not validated, and rightly. Folding of two
  constants survives where the host's NaN is the target's (P1-8).
- What it costs: a rule for NaN for each target, read against the
  manuals of the processors, with payloads, which `SpecFloat` has
  not got (its NaN is one value); and an assumption on the backend
  that nothing checks, that it keeps the order of the operands of an
  operation that commutes on numbers. The four identities, or their
  comment, change in the compiler.

**Option 2: floats up to the payload and the sign of NaNs.** There is
one NaN as far as arithmetic goes.
- What `eval_prim` returns on a NaN: arithmetic that is given or
  makes a NaN returns one canonical NaN; a NaN that is a constant of
  the term keeps its bits, and `Abs` and `Neg` change the sign bit
  only. Two floats are then compared up to "both are NaN" wherever an
  outcome holds one: a float that is returned, one in a boxed number,
  in a field of a block, in a static constant and, with the heap, in
  a cell. A primitive or a call that reads the bits or the sign of a
  NaN (`Reinterpret_64_bit_word`, a store into a string or a
  bigarray, `Float.sign_bit`, `copysign`) has no value on one: a part
  of the language left out on purpose, with a CR at each.
- Which identities survive: all six, and folding on any host.
- What it costs: the relation between values and between outcomes
  changes, which is the core's and the heap's and not the exits'
  alone (the shape of the rule for poison, D26). The types must
  follow: a type that says a variable is exactly one float constant
  means a bit pattern today. A program that reads the sign of a NaN
  is undefined in the model, and such programs exist: the
  reproduction of P1-7 with `Float.sign_bit` is one. The comment in
  Simplify changes.

Between the two there is a stage that is neither: canonical NaNs with
no change to the relation. It is an abstraction that does not match
the compiler: Simplify folds with the host's NaN and keeps the bits
of constants, so on a unit that makes a NaN the model and Simplify
can differ with no bug in the compiler, and such a unit is outside
what the comparison of runs can judge. And one option that is too
permissive to keep: an operation whose result is a NaN has no value,
after which anything refines the term.

## What does not depend on the choice

`SpecFloat`, on bit patterns, at both widths, with no dependency and
no axiom: binary and unary `Float_arith`, `Float_comp` and `Num_conv`
with floats, on floats that are not NaN, with signed zeros distinct;
`Abs` and `Neg` on the sign bit; comparisons with a NaN, which do not
look at which NaN it is; differential tests against Simplify on
values that are not NaN (signed zeros, subnormals, infinities and the
rounding cases). What arithmetic returns when it is given or makes a
NaN is the one case of `eval_prim` that waits for the choice. None of
it lands before the human has read this.

Asked of the human: the choice between the two options (the CR
above); whether a test that depends on the host's floats is
acceptable in the tree; whether `float32` is wanted now.

Reviewed as a design by R2 (2026-11-12), whose points are taken above:
canonical NaNs alone are a mismatch of abstraction; comparing up to
NaN reaches boxed numbers, static data, the heap and the types; `Abs`
and `Neg` are outside the rule for NaN; signed zeros stay distinct;
what is undefined is left out on purpose; the three suspected
differences are recorded, and said to be of the compiler only as far
as each is shown. No addition to the trust ledger is asked or agreed.
