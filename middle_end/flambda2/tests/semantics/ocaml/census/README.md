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
mutable, no float, no string and no exception, but in the two
profiles of the last section.

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
| `unknown_scalar` | 150 | 149 | 1 |
| `known` | 100 | 98 | 2 |
| `unknown` | 100 | 98 | 2 |
| `functions` | 100 | 97 | 3 |

592 of the 600 are validated. On the same 600 terms, earlier the
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
second asking are validated at the first. Two more with two arms of
a `Switch` that give one continuation 0 and 1 made the tagging of
what is tested (`FlambdaMergeSwitchesSpec.merge_switches`;
`functions`, seed 5, and `unknown_scalar`, seed 38), and four more
with the applications of a continuation of no parameters whose
handler is one jump forwarded in the term after
(`FlambdaForwardJumpsSpec.forward_jumps`; `functions`, seeds 14, 27
and 72, the last at the second asking, and `unknown_scalar`, seed
100). Sharing the projections of value slots changes none, and nor
does the unboxing of parameters giving, for an untagging under a
test, the number that was tagged. One more with that unboxing
giving a constant where a symbol of a constant block would be
untagged (`unknown_scalar`, seed 1). Two more with the rewrites
that Simplify makes from the types applied once to the term before
(`FlambdaSimplifyPassSpec.simplify_by_types`; `unknown_scalar`,
seeds 57 and 61). Reading the value slots that every closure of the
unit gives one symbol changes none. One more with the
continuations of each term placed once the rounds are over
(`FlambdaValidateSpec.placed`; `functions`, seed 65), and the unit
that was validated at the second asking is validated at the first.
The sharing of primitives knowing, under an untagging, that the
variable untagged is the tagging of the result changes none, and nor
does the test against zero of a three-way comparison made the
comparison of its operands
(`FlambdaRecoverComparisonSpec.recover_known_comparisons`), nor the
tidying of each term once its continuations are placed
(`FlambdaValidateSpec.tidied_before`), nor the static blocks in
scope known where a parameter is unboxed
(`FlambdaUnboxInScopeSpec.v`), nor the second asking following
aliases in the bodies of code. These 600 units import nothing, so
the tool prints of each what it printed. No unit
that was validated at one of these points is not at a later one. The
day before, 336 were validated, 256 were not and 8 were not checked;
of the units that keep a function, none was.

What the 8 units that are not validated lack, read off the two
terms that the tool shows of each:

| What is missing | `unknown_scalar` (1) | The other three (7) |
|-----------------|----------------------|---------------------|
| A block that Simplify makes a symbol and the term before still makes with a `Let`: the block is made in a handler and Simplify binds the symbol outside it, or the guess of the tool does not find it | 0 | 7 |
| A `Switch` that Simplify removes with what it knows of the variable tested | 1 | 0 |

The unit of the second row (seed 144) has two things. Two arms of
a `Switch` give one continuation two arguments, each the number of
the arm, where the term after has no such continuation; and below
it a `Switch` is on a variable that a `Switch` around it has tested.

Five of the 600 have the constant `poison` after Simplify, which
unboxes a variant where two branches meet and gives the fields that a
branch has not got that constant. The conversion makes it the poison
of the model, so they are run and compared; four are validated
(`functions`, seeds 27 and 55; `unknown_scalar`, seeds 1 and 100),
and the other is in the second row.

In five of the 8 the term before keeps a continuation that the
term after has not: the one of the second row, and four where a
handler only makes a block and goes on (Simplify makes the block a
symbol and has no use for the handler).

The first row is in the tool only: nothing is believed of its
guesses, and a better one needs no proof.

So, for units of this kind: when every input is known and the result
is a number, all are validated; with unknown inputs and numbers, 149
of 150; of the units that keep a function, 97 of 100.

## Two more profiles: exceptions, loops

`exceptions` is `unknown` with handlers: `try ... with _ ->`, `raise
Not_found`, `raise_notrace`, and `/` and `mod`, which raise where the
divisor is zero, under a handler; an inlined function may raise, and
is then called under a handler. `loops` is `unknown` with `for` loops
(up and down) and `while` loops on references, local recursive
functions (whose recursive call is a tail call or not), and one
recursive function that the unit keeps and exports. With `_scalar`
the values of the unit are integers and booleans, as above. The
bounds of the loops, and the number of times that a recursive
function is first asked to go round by the unit itself, are chosen
from 0 to 6, and the generator nests loops twice at most. The
function that the unit exports takes any number.

    sh census/run.sh <ocamlopt> <flsemantics.exe> 1 60 census-output \
      exceptions exceptions_scalar loops loops_scalar

Seeds 1 to 60 of each, 240 units, on 2026-11-12. No unit on which the
two runs differ, none undefined before Simplify, none on which the
tool gave no answer.

| Profile | Units | Validated | Validated with its imports | Validated with nothing imported only | Not validated | Not checked |
|---------|-------|-----------|----------------------------|--------------------------------------|---------------|-------------|
| `exceptions` | 60 | 33 | 13 | 14 | 0 | 0 |
| `exceptions_scalar` | 60 | 34 | 23 | 0 | 3 | 0 |
| `loops` | 60 | 36 | 0 | 0 | 22 | 2 |
| `loops_scalar` | 60 | 36 | 0 | 0 | 24 | 0 |

A unit that names a predefined exception has an import, and the
tool runs it from its imports (`../README.md`, "What the verdicts
mean"): 51 of the 120 units with exceptions. The validator accepts
50 of them, as it did before the tool ran units so. 36 are accepted
with a verdict that is proved of the two units run from their
imports. The other 14, all in the profile that keeps a function,
are accepted once closures are lifted, which is proved of the two
units run with nothing imported only: they are not validated with
their imports. One of the three units that are not validated has an
import. The validator accepts 189 of the 240, as it did; 139 of
them import nothing.

The two that are not checked have a reference that a local function
captures: it stays a block with a field that is written
(`Block_set`).

Before each term that is compared had its continuations placed
(`FlambdaValidateSpec.placed`), 16 of the 120 units with loops were
validated, and in 57 of the 102 that were not the two terms had,
once the names are erased, the same lines in another order. The
common case is the return continuation of a call that does not use
its parameter, as in

    let rec f n acc =
      if n <= 0 then acc else (let _ = f (n - 1) acc in n)

The term before binds the continuation and then has the `Let` of
`n - 1`; the term after has the `Let` first. Simplify cannot remove
the parameter of a return continuation, so it makes a wrapper of
the continuation at the call, below the `Let`s of the arguments,
and the handler, which is then applied once, ends up there. The
placing moves the continuation of the term before down to the call.

What the 46 units with loops that are not validated lack. One unit
of each kind was read; the counts are of the units whose two terms,
as the tool shows them, differ by the same kinds of line.

- A closure of no value slot that the term before makes by a `Let`
  and the term after has as a symbol (17 units). A local recursive
  function that captures nothing, in the code of a function that
  the unit keeps or in a handler: Simplify binds its closure with
  its code, and where the function around it is inlined twice the
  two `Let`s are one symbol.
- Code that the term after has twice or more (10 units). An inlined
  function with a local recursive function that captures one of its
  parameters, called twice. Simplify copies the code at each
  inlining, makes each closure a symbol and puts the constant of its
  value slot in its copy of the code; the term before has one piece
  of code and two closures.
- The return continuation of a call, whose handler only applies
  another continuation (7 units): the term before keeps it, and in
  the term after the call returns to the other.
- A closure with a value slot that is a variable, which Simplify
  makes a symbol in the handler where the variable is bound (4
  units).
- Eight others. One has a `Let` on the other side of the binding of
  a recursive continuation, one has static bindings in another
  place, and six differ by continuations or by a `Switch`, and were
  not sorted further.

Of the three units with exceptions that are not validated, one has
the same lines in another order: a `Let` is on the other side of the
binding of a continuation that the placing does not move. One has a
comparison in the term after whose result nothing uses, which the
term before has lost. One has, in the term after, a record that
Simplify made a symbol and a load of a field of that symbol, where
the validator has the field: the record is the result of a `try`
whose handler gives another record, and the handler turns out not to
be reached.
