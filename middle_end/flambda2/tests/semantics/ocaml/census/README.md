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
| `unknown_scalar` | 150 | 144 | 6 |
| `known` | 100 | 98 | 2 |
| `unknown` | 100 | 98 | 2 |
| `functions` | 100 | 92 | 8 |

582 of the 600 are validated. On the same 600 terms, earlier the
same day: 509 before the term after lost the continuations that are
applied once (`FlambdaValidateSpec.inline_once_applied_after`); 555
with that, and still 555 with the unused `Let`s of the parameters of
code removed from the term after; 577 with the tool guessing again
what was lifted where its first guess gave a symbol to a block that
nothing uses, and with the lifting out of the code of functions; 578
with the second asking (`unknown`, seed 30); and four more with the
constants lifted to the head of the unit and the parameters of
continuations unboxed where branches meet (`functions`, seeds 1, 55
and 69; `unknown_scalar`, seed 122). Sharing the loads marked
immutable changes none, and nor does the demotion of exception
handlers, which the generated units have not got; with the rounds
gone through again after it, the two units that were validated at the
second asking are validated at the first. No unit that was validated
at one of these points is not at a later one. The day before, 336
were validated, 256 were not and 8 were not checked; of the units
that keep a function, none was.

What the 18 units that are not validated lack, read off the two
terms that the tool shows of each (a unit may lack more than one):

| What is missing | `unknown_scalar` (6) | The other three (12) |
|-----------------|----------------------|----------------------|
| A block that Simplify makes a symbol and the term before still makes with a `Let`: the block is made in a handler and Simplify binds the symbol outside it, or the guess of the tool does not find it | 0 | 7 |
| A `Switch` that Simplify removes with what it knows of the variable tested | 5 | 1 |
| A continuation whose handler is one jump, applied by an arm of a `Switch` and by another handler: Simplify keeps it, and the first phase of the term before sends each application where the jump goes | 1 | 3 |
| A `Let` on the other side of the binding of a continuation whose handler does not use it | 0 | 3 |

The second row is three things, and a unit may have more than one.
Two arms that give one continuation 0 and 1 are made the tagging of
what is tested (three units have a tagging in the term after that the
term before has not). A `Switch` on a variable that a `Switch` around
it has tested, or on the untagging of such a tagging, is resolved. A
match on a variant that was made where two branches meet loses its
tests where one branch gives a symbol of a static block, which the
unboxing of the validator does not read under a test (two units).

Five of the 600 have the constant `poison` after Simplify, which
unboxes a variant where two branches meet and gives the fields that a
branch has not got that constant. The conversion makes it the poison
of the model, so they are run and compared; one is validated
(`functions`, seed 55), and the other four are in the rows above.

In ten of the 18 the term before keeps a continuation that the term
after has not: the six of the second row, and four where a handler
only makes a block and goes on (Simplify makes the block a symbol and
has no use for the handler).

The first row is in the tool only: nothing is believed of its
guesses, and a better one needs no proof.

So, for units of this kind: when every input is known and the result
is a number, all are validated; with unknown inputs and numbers, 144
of 150; of the units that keep a function, 92 of 100.
