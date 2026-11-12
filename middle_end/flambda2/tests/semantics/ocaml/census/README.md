# A count over generated units

The examples of the directory above are written by hand, and most are
written to validate. This is the other measure: units made at random,
with what the test tool says of each.

    sh census/run.sh <ocamlopt> <flsemantics.exe> 1 150 census-output

run from the directory above, makes for each seed from 1 to 150 one
unit of each profile (`gen.py`), makes its term (`from_ocaml.sh`), runs
the tool on it and prints the counts. Nothing here is run by the tests.

## What a generated unit is

One to three inlined functions of two integers and a boolean, each
returning an integer, a boolean, an option, a pair, a variant or a
record; then one to three values that call each of them and compute
with the results. The expressions are arithmetic and comparisons on
integers, boolean operators, conditionals, constructors and matches on
the variant, on options and on pairs, record fields, `let`, and
closures applied at once. There is no recursion, no loop, nothing
mutable, no float, no string and no exception.

The profiles: `known` (every input is a constant), `unknown` (about a
quarter of the integer constants are behind `opaque`), `functions`
(as `unknown`, and the unit keeps one or two functions that are not
inlined). With `_scalar` the values of the unit are integers and
booleans only; without it, about four in ten are an option, a pair or
a variant, that is, a block that the unit keeps.

## The counts of 2026-11-12

Seeds 1 to 100 for the first three profiles, 1 to 150 for the two
scalar ones: 600 units. No unit on which the two runs differ, none
undefined before Simplify, none on which the tool gave no answer, none
that the conversion refused.

| Profile | Units | Validated | Not validated |
|---------|-------|-----------|---------------|
| `known_scalar` | 150 | 150 | 0 |
| `unknown_scalar` | 150 | 124 | 26 |
| `known` | 100 | 94 | 6 |
| `unknown` | 100 | 76 | 24 |
| `functions` | 100 | 65 | 35 |

509 of the 600 are validated. The day before, with the validator as it
then was, 336 were, 256 were not and 8 were not checked; of the units
that keep a function, none was.

What the 91 units that are not validated lack, read off the two
normalised terms by a script (a unit may lack more than one):

| What is missing | `unknown_scalar` (26) | The other three (65) |
|-----------------|-----------------------|----------------------|
| The term after keeps a continuation that is applied once, which its normalisation does not inline | 20 | 30 |
| A block with a field that is not known until the module runs, which Simplify makes a symbol: the guess of the tool gives the symbol to another `Let` of a block of the same shape | 2 | 35 |
| A `Switch` whose two arms give one continuation 0 and 1, which Simplify makes the tagging of what is tested | 6 | 9 |
| The term before keeps a continuation that the term after has not | 5 | 7 |
| In the code of a function that stays, a `Let` of a parameter that nothing uses, left in the term after | 0 | 3 |

The first row is a rewrite that exists and is not in the
normalisation of the term after yet
(`FlambdaInlineTailSpec.inline_tail_conts_kinded`). The second is in
the tool only: nothing is believed of its guesses, and a better one
needs no proof. The last is the removal of a `Let` that is sure to
have a value, which in the body of code does not know the kinds of
the parameters.

In five units the term after Simplify has the constant `poison`
(Simplify unboxes a variant where two branches meet, and gives the
fields that a branch has not got that constant). The conversion makes
it the poison of the model, so they are run and compared; none of the
five is validated, each for one of the rows above as well.

So, for units of this kind: when every input is known and the result
is a number, all are validated. With unknown inputs, what stops a unit
is, more than half the time, a continuation applied once that Simplify
leaves and the validator inlines on one side only. A unit that keeps a
block made of values that are not known waits for a better guess of
what was lifted.
