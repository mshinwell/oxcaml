# A refinement proved on the machine of terms, and regions

For whoever has a statement about a pass (a rewrite, a rebuild of a unit)
that is a refinement on the machine of `semantics/FlambdaSemanticsSpec.v`,
and wants it to say something of a unit that has regions. Nothing on this
page is a statement: the statements are in the files that it names, and
it says in what order they are used.

## What the machine of terms does with regions

It has none (decision D37). `FlambdaPrimitiveSpec.eval_prim` gives no
value to a primitive of regions (`Begin_region`, `Begin_try_region`,
`End_region`, `End_try_region`, `Local_allocation`), so the run of a term
is undefined at the `Let` of one. `refines` asks nothing of a source that
goes wrong. So `refines` from a state whose run comes to such a `Let`,
and `unit_refines` from a unit whose run does, hold whatever the other
is: the refinement is true, and it says nothing of that unit.

The machine of `regions/machine/FlambdaRegionsSpec.v` runs such a unit.
No relation of refinement is defined on it, and no law of renaming is
stated of it (its header, "what is not stated"): what is proved of a
pass is proved on the machine of terms, and carried.

## What to prove on the machine of terms

The refinement of the two units with their regions dropped, each run from
the static environment of its imports:

    unit_refines imports (erase [] before) (erase [] after)

`FlambdaRegionsSpec.erase` drops the `Let` of a begin, has that of an end
bind the unit value, makes a `Local_allocation` an alias or nothing, and
drops a parameter of the kind `Region` with the argument at its place in
every `Apply_cont` of its continuation. It leaves a primitive of regions
only where it is not applied as the conversion of the test tool applies
it.

Where the statement is of two terms that are `erase` of the units only up
to bound names (the test tool converts a unit twice, once with its
regions dropped), the comparison `FlambdaCompareSpec.expr_eqb` is sound
and `refines` is transitive: the two statements of
`regions/check/FlambdaRegionsCheckSoundSpec.v` whose names begin
`validated_and_checked` are made so, from a verdict of the validation.

## What follows on the machine of regions

Two statements of `regions/check/FlambdaRegionsCheckSoundSpec.v`, of the
two units as they are, regions and all, run on the machine of regions
from the static environment of their imports.

- `unit_refined_and_checked_safe_statement`: the unit after never stops
  without a step, for a rule of regions or where `step` has none.
- `unit_refined_and_checked_exits_agree_statement`: an exit of the unit
  before is an exit of the unit after, through the same continuation,
  with values that are erased to the same values where they may be
  evaluated or are locations.

Their premises, beside the refinement:

- The unit before, with its regions dropped, does not go wrong. Of one
  that does, they say nothing, as the refinement says nothing.
- The unit after passes the check of regions
  (`FlambdaRegionsCheckSpec.region_check`) with some certificate. The
  check is a test of that unit alone and runs nothing; nothing is asked
  of the certificate but that the check passes with it.
- The symbols that the machine of regions draws, from `base` on, are none
  of the unit or of its imports, and the static environment holds no
  location (`FlambdaRegionsSpec.region_names_fresh`); and the unit is one
  that the erasure is meant for (`FlambdaRegionsSpec.erasable`: no call
  returns or raises to a handler that has a region parameter, no handler
  states anything of a parameter that is a region, and there is no poison
  constant of the kind `Region`). The first statement asks these two of
  the unit after, the second of both units.

What the check is for: the regions of a unit that passes it add no fault
to the unit (`FlambdaRegionsCheckSpec.regions_add_no_fault`, by
`region_check_sound_statement`): where its run on the machine of regions
stops without a step, its run with its regions dropped goes wrong too.
The two statements of `FlambdaRegionsCheckSpec.v` that take this for a
premise in the place of the check (`checked_after_safe_statement`,
`checked_exits_agree_statement`) have `refines` of two states for the
refinement. `unit_refines` of the two units with their regions dropped
is that `refines` at the static environment of the imports: one
proposition, by computation.

## Where the statement about the pass is less than `refines`

A pass that removes what nothing reads, as the rebuild of the reaper
does, need not give `refines`: the unit after may exit with closures
that have fewer value slots, and with other cells in its heap. A
statement about such a pass compares the exits of the two units in one
of three ways:

1. The exits are equal: `refines`, `unit_refines`. The two statements
   above are for it.
2. The heaps are equal and the values are related by less than equality:
   closures are compared without their value slots, say.
3. The values and the heaps are related up to a correspondence of the
   locations of the two heaps.

For the second and the third, two statements of the same file,
`related_and_checked_safe_statement` and
`related_and_checked_exits_statement`, take what the two above use of
`refines` and no more. They are of any static environment; at that of
the imports, `erased_initial_state e statics` is the state from which
`unit_refines` runs `erase [] e`.

- `erased_after_wrong_only_if_before`: where the unit after, with its
  regions dropped, goes wrong, the unit before, with its regions dropped,
  does. For "never stops without a step" it is the only premise about
  the pass. A statement of any of the three kinds gives it, if it says
  that the unit after goes wrong only where the unit before does.
- `erased_exits_related R`: an exit of the unit before, with its regions
  dropped, is matched by an exit of the unit after, with its regions
  dropped, through the same continuation, and `R` holds of the values and
  the heaps of the two. `R` is the comparison of the statement about the
  pass: for the second kind, the same heap and the values related; for
  the third, the relation of values and heaps up to the correspondence.

Given an exit of the unit before with its regions, the statement of the
exits supplies an exit of the unit after at the same continuation. It
also supplies an exit of each erased unit at that continuation. The
values of each run with regions are related to the values of its own
erased exit by `value_erased_if_usable`; `R` holds of the values and
heaps of the two erased exits. This does not give `R` of the values or
heaps of the runs with regions.

`refines` gives the two premises, with equality of values and heap for
`R` (`refines_erased_related_statement`). The two statements of a unit,
above, are proved using this instance. In the statement of the exits of
that pair, the two lists of values of the runs with regions are related
to one common list of erased values.

## What does not follow

- No safety conclusion for the unit before with its regions, and no
  premise that it pass `region_check`. The second statement still asks
  `region_names_fresh` and `erasable` of it. If its run with its regions
  stops without a step, that statement has no exit to match.
- No refinement on the machine of regions. The second statement goes one
  way, from an exit of the unit before to one of the unit after, and the
  values at the two exits are related, not equal: the header of
  `regions/erasure/FlambdaRegionsErasureSpec.v` says what the relation
  leaves out.
- Nothing of a region that is not ended: leaving code with a region of
  its own still open is no fault of the machine (decision D48).
  `regions/ends/FlambdaRegionsEndsSpec.v` is about the ends.
- Nothing that the test tool prints. The tool does not ask
  `region_check`; its line about regions is of one run of each unit on
  the machine of regions (`rocq/TRUST-LEDGER.md`, the entry "The check of
  regions"). And the check is not complete: it refuses units that the
  machine runs to their end.
