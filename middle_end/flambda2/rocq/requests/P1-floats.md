# P1: floating-point arithmetic in the model. A request

Owner: P1. For the human. Nothing here is done: this says what the
model would need for floats, what each way of getting it costs, and
what I recommend. Four of V2's units stop on floats today
(`float_add.ml` and two like it on `+.`, one on `float_of_int`).

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

Three places where I expect the machine not to agree with it, none
tried yet (each is a short `.ml` test for X2 or X5):
1. Which NaN an operation returns is the host's. x86-64 gives the
   negative quiet NaN for `0. /. 0.`, arm64 the positive one; for two
   NaN operands the result depends on the order the backend gives the
   instruction its operands.
2. `x *. 1.` of a signalling NaN is that NaN made quiet on the
   machine, and `x` in Simplify.
3. `x *. -1.` of a NaN keeps its sign on the machine, and `Neg x`
   flips it.

## What the model needs

1. Operations on bit patterns: decode to sign, exponent and mantissa,
   compute with rounding to nearest even, encode; at 64 and at 32
   bits. `Abs` and `Neg` are operations on the sign bit.
2. Comparison with NaN unordered, and the total order for `compare`.
3. Conversions: integer to float (rounded), float to integer
   (truncated), between the two widths.
4. A rule for NaN results (below).
5. A rule for a conversion to an integer of a NaN or of a float out of
   range: OCaml leaves it unspecified and x86-64 and arm64 differ. I
   would make it undefined, with a CR.

## Where the arithmetic would come from

| Source | Has | Adds to the trust ledger |
|--------|-----|--------------------------|
| `Corelib.Floats.SpecFloat` (in the installed Rocq) | IEEE 754 in Rocq on integers, any precision, so 64 and 32 bits; one NaN, no payload; `SFadd`, `SFmul`, `SFdiv`, `SFcompare`, rounding to nearest even | Nothing: definitions only. It is the specification one reads. About 80 lines of ours for bit patterns and conversions |
| `PrimFloat` (the kernel's machine floats) | 64 bits only; fast; one NaN | To prove anything, the 22 axioms of `FloatAxioms.v`. To run, the extraction to OCaml's floats, that is the host's, as Simplify uses: the test would compare the host with itself |
| Flocq (not installed) | 64 and 32 bits, NaN payloads, the rule for NaN as a parameter, proofs against the reals; what CompCert uses, with a rule per target | A new dependency of `make -C rocq`; proofs through it use the axioms of Rocq's reals |

## The rule for NaN, which is the decision

The machine of the model is a function, and which NaN the hardware
returns is not fixed by the term (point 1 above). The options:
- (a) An operation whose result is a NaN has no value. Simple, and too
  permissive: after such an operation anything refines the term.
- (b) Every NaN result is one canonical NaN. Then the model and
  Simplify, which has the host's NaN, differ in the bits, and a unit
  that makes a NaN fails the comparison of runs.
- (c) As (b), and an exit compares floats up to "both are NaN"; a
  primitive that reads the bits of a NaN (`Reinterpret_64_bit_word`,
  a store into a string) has no value on one, with a CR. This is the
  shape of the rule for poison (D26), and changes the relation at an
  exit, which is the core's.
- (d) The rule of one target (x86-64), as CompCert has a rule per
  target. Exact for one backend if the order of operands is known,
  which it is not at this level.

## Recommendation

`SpecFloat`, on bit patterns, at both widths: no dependency and no
axiom. For NaN, (c). First step, leaf work in the primitives' files
once the human agrees: binary and unary `Float_arith`, `Float_comp`
and `Num_conv` with floats, with (b) until the core has the relation
of (c), and differential tests against Simplify on values that are
not NaN (with signed zeros, subnormals, infinities and the rounding
cases). The three tests above go to X2 or X5 first: if the compiler's
developers want (d), the choice changes.

Asked of the human: the choice among (a) to (d); whether a test that
depends on the host's floats is acceptable in the tree; whether
`float32` is wanted now.
