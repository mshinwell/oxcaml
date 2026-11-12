# S6: unboxing of continuation parameters, on the validator's side

A request with a prototype, from T6. Reviewer: R5. Immutable cases
only. It says what Simplify does, what the two terms of a unit look
like where it has unboxed a parameter, which rewrite the validator
needs and on which side, what is built, and what is asked of the model
and of other streams before the rest can be.

Summary.

- The rewrite is for the term before, and is a refinement. An
  after-side rewrite that puts a load back into the handler does not
  apply to the common case, in which the boxed parameter is gone
  (section 3).
- One pass is built and proved: `FlambdaUnboxParamsSpec.unbox_known_params`.
  It covers every unboxing in which each application gives arguments
  that are already in scope: pairs, records, boxed numbers and tagged
  immediates that every path builds, and the `is_int` and tag
  parameters of a variant (section 4). Two bodies of code from OCaml
  sources are validated with it in Rocq, and are not without it.
- Where one application gives a block that the term does not show (a
  parameter of the function, the result of a call, the entry of a
  loop), Simplify adds a load that is justified by a subkind. The model
  has no subkinds; there the term after is less defined than the term
  before, and no rewrite on either side can be proved. This is the
  first thing asked (section 5).
- Variants need no statement about poison and no answer on D26. A
  second pass is built and proved for them:
  `FlambdaUnboxVariantsSpec.unbox_variant_params`. It makes a
  parameter of a read that is under a test, and gives a constant in
  place of the read at an application that the term shows not to come
  to the read, or on whose argument the read has no value: `None`, `[]`,
  a constant constructor, a block of another tag. Seven bodies of code
  from OCaml sources are validated with it in Rocq, with Simplify's
  `poison` where the pass puts it, and are not without it. It has its
  statements of renaming and of scope, and the validation runs it, in
  the first phase of the term before: nine units from OCaml sources
  that were not validated are (sections 7 and 9).

## 1. What Simplify does

Read from `middle_end/flambda2/simplify/unboxing/` and
`simplify/simplify_let_cont_expr.ml`, `simplify/join_points.ml`,
`simplify/apply_cont_rewrite.ml`,
`simplify/continuation_extra_params_and_args.ml`.

**Which continuations.** The parameters of a continuation are
considered for unboxing when its handler is about to be simplified
(`prepare_dacc_for_handlers`, `simplify_handler`). Never: a return
continuation, an exception handler, or a continuation with a single
use that is inlined (the typing environment of the use already knows
the fields).

**The decision** (`Optimistic_unboxing_decision.make_optimistic_decision`)
is taken from the type of the parameter alone, to a bounded depth:

- a boxed or tagged number (`prove_is_a_boxed_number`, one decider for
  each kind of number): one new parameter, the number;
- a block of one tag and one size (`prove_unique_tag_and_size`): one
  new parameter for each field, and the decision again for each field;
- a variant (`prove_variant_like`), for a non-recursive continuation
  only: a parameter for the tag, one for `is_int` and one for the
  constant constructor if there are constant constructors, and one for
  each field of each tag;
- a closure with a single entry, for a non-recursive continuation
  only: one parameter for each value slot.

The type of the parameter of a non-recursive continuation is the join
of the types of the arguments at its uses, each met with what the
subkind of the parameter says (`Join_points.add_equations_on_params`).
For a recursive continuation it is what the subkind says and nothing
else (`Downwards_env.add_parameters_with_unknown_types`), and the
decision is kept without looking at the uses. For a non-recursive one
the decision is then refined at each use and dropped where it is of no
benefit (`Is_unboxing_beneficial`: some use must give a field that is
already in scope).

**The extra arguments** (`Unboxing_epa.unbox_arg`), one for each new
parameter at each use:

- where the type of the argument at the use knows the field (the
  prover of the unboxer answers `Known_result`): the field itself, an
  argument that is already in scope;
- where it does not (`Need_meet`): a new variable bound just before
  the application to the unboxing primitive applied to the argument.
  For a field it is `Block_load` marked `Immutable`, with the tag and
  the size of the decision in its access kind (`Unboxers.Field`); for a
  number `Unbox_number` or `Untag_immediate`. An arm of a `Switch`
  gets a wrapper continuation that holds these bindings;
- for a variant, at a use where the argument is a constant constructor
  or a block of another tag: the tag and `is_int` are constants, and
  each field of the tags that the argument has not is the constant
  `poison` of the kind of the field (`Const.const_poison`; the constant
  zero for a field of the value prefix of a mixed block).

The new parameters come after the old ones, and in the reverse of the
order in which the decision lists them, as each is put first
(`Continuation_extra_params_and_args.add`): the last field first.

**The handler** is simplified with the type of the old parameter
saying that its fields are the new parameters
(`Build_unboxing_denv.denv_of_decision`: an immutable block of aliases;
for a variant also `Get_tag` and `Is_int` of the parameter, by CSE and
by the two relations). So every load of a field in the handler becomes
the new parameter. The old parameter stays a parameter. If the handler,
once rebuilt, does not use it, it is removed with its arguments like
any unused parameter (`Apply_cont_rewrite`), and an allocation at a use
that was made only to be passed goes with it.

A comment in `unboxing_epa.ml` (at the fields of a variant) refers to
`doc/unboxing.md` for invalid constants, poison and aliases. There is
no such file in the tree.

## 2. What the two terms look like

Measured on the sources of section 9, with the test tool of
`middle_end/flambda2/tests/tools/` printing the two terms that the
validation compares. Names are shortened.

**A pair built on both paths** (`pair_built`; `pair_computed` is the
same with an addition in each branch, which then stays a
continuation). Before, as the validation normalises it today:

    let_cont k (p) =
      let f1 = Block_load 1 (p) in
      let f0 = Block_load 0 (p) in
      let s = add (f0, f1) in cont ret (s)
    in
    let_cont k0 () = let b = Make_block 0 (2, x) in cont k (b) in
    let_cont k1 () = let b = Make_block 0 (x, 1) in cont k (b) in
    switch c | 0 -> cont k0 () | 1 -> cont k1 ()

After:

    let_cont k (f1, f0) = let s = add (f0, f1) in cont ret (s) in
    switch c | 0 -> cont k (x, 2) | 1 -> cont k (1, x)

The boxed parameter is gone, no block is made, and no load is left.

**A pair that one path is given** (`pair_join`: one use gives a
parameter of the function). After:

    let_cont k (f1, f0) = let s = add (f0, f1) in cont ret (s) in
    let_cont k0 () =
      let g0 = Block_load[tag 0, size 2] 0 (pair) in
      let g1 = Block_load[tag 0, size 2] 1 (pair) in
      cont k (g1, g0)
    in
    switch c | 0 -> cont k0 () | 1 -> cont k (2, 1)

The loads at the use have the tag and the size in their access kind.
Those of the handler before have neither (`%block_load.[0]`, as the
front end makes them for `fst` and for a pattern).

**A pair that is also returned** (`pair_kept`): as the last, with the
boxed parameter kept first: `k (p, f1, f0)`, `cont k (pair, g1, g0)`,
`cont k ($block, 2, 1)`.

**A boxed number** (`int64_built`, `int64_join`): the same shapes with
`Unbox_number` for the load and `Box_number` for the block.

**A loop** (`pair_loop`, a tail-recursive function with a pair as its
accumulator): the loop continuation has the two fields as parameters
and not the pair; the entry of the loop loads them from the parameter
of the function, with the tag and the size; the jump round the loop
gives the two fields it computed.

**A variant** (`option_join`): the handler takes `is_int` and the
field; the use that gives `None` passes `1` and `poison`, the use that
gives `Some` passes `0` and the field.

## 3. Which side, and why

The validation normalises the term before by rewrites that refine it
and the term after by rewrites that are equivalences, and compares
(`FlambdaValidateSpec.v`). What the chain needs of a rewrite `R` of
the term after is that the term after refines `R (after)`: it may make
the term less defined, never more. A rewrite of the term before may
make it more defined, never less.

The suggestion to test was an after-side normalisation: remove an
extra parameter that every use gives as the load of a field of another
argument, and put that load at the head of the handler. Findings:

1. It needs the boxed argument to be there to load from. In the
   common case, which is the one in which unboxing pays, the boxed
   parameter is unused once the loads are replaced and Simplify has
   removed it (`pair_built`, `pair_join`, `int64_built`, the loop). The
   after side would have to make the block again at each use, with a
   tag, a size and an order of fields that the term after does not
   have. That is inventing the term before.
2. Where the boxed parameter is kept (`pair_kept`), the rewrite applies
   and is an equivalence, taken as one step: the load is done just
   before the jump or just after it, and nothing can be observed
   between the two. But the load it puts in the handler has the access
   kind of the load at the use, with a tag and a size, and the handler
   before has a load without them. The comparison still fails, for the
   reason of section 5.
3. Going the other way with the same step, on the term before, takes
   the load at the head of the handler to the uses. That is what
   Simplify does, it needs nothing invented, and with what the
   validation already has it reaches Simplify's term: the load at a
   use of a block made there is resolved by `load_known_blocks`, the
   boxed parameter that the handler no longer uses is removed by
   `drop_unused_params`, the allocation left unused by
   `remove_unused_lets`, and a handler left with only a jump by
   `shortcut_switches`.

So the rewrite is on the side of the term before. It is stated as a
refinement, which is what that side needs. It is not an equivalence in
general: section 4, "The statement".

## 4. What is built: `unbox_known_params`

`FlambdaUnboxParamsSpec.v`, proofs in `FlambdaUnboxParamsProofs.v`.

At a non-recursive `Let_cont k` whose handler begins with

    Let f kind (Prim (Unary p) [Var x])

where `x` is a parameter and `p` reads a box (a `Block_load` not marked
`Mutable`, `Is_int`, `Get_tag`, `Unbox_number`, `Untag_immediate`), the
`Let` is removed and `f` becomes one more parameter, the last. Every
application of `k` in the body of the `Let_cont`, inside the handlers
of other continuations and in the arms of a `Switch` too, gets one
more argument, the last: what `p` is known to give of the argument it
has for `x`. That is known from the term alone, in the three ways the
validation already has:

- the argument is a variable bound to a `Make_block`, or a symbol bound
  to a static block (`FlambdaBlockLoadSpec.load_known_named`);
- it is a variable bound to a `Box_number` or a `Tag_immediate`, or a
  symbol bound to a static boxed number
  (`FlambdaUnboxSpec.unbox_known_named`);
- it is a constant on which the primitive has a value
  (`FlambdaNormaliseSpec.fold_named`).

If some application does not say, if an `Apply` returns or raises to
`k`, or if `k` is an exception handler, nothing is done. Then the same
is done for the `Let` that the handler now begins with, so the fields
of a pair, or a field of a field, all become parameters. No name is
made (`f` was bound at the head of the handler and is bound as a
parameter), and no `Let` is added at an application.

This is Simplify's unboxing where every extra argument is "already in
scope". It is the same step for a field, for a number, and for the tag
and `is_int` of a variant.

**The statement.** `unbox_known_params_refines_statement`: for every
term `e`, `expr_refines e (unbox_known_params e)`, under all
environments, with no premise. It is a refinement and not an
equivalence. A case in which it is not: a static block may hold a
field that is not of the kind of values, as nothing tests the fields
of a static block when it is bound. `load_known_named` gives what that
field holds; the load in the handler has no value on it; and after the
pass the application gives the field to a new parameter of its kind,
so the term after runs where the term before is undefined. (Where the
access kind disagrees with the known block, or asks for an immediate,
`field_loaded` gives nothing and the pass does not fire.)

**The proof.** The rewrite changes a handler and all its applications
together, so it is a simulation over states. The second run takes one
step fewer at each application of the continuation (there is no `Let`
left to run), so the lemma of `FlambdaSimulationProofs.v`, in which
the second run is the one that takes more steps, does not serve. The
Proofs file has the other form (`ahead_refines`: a step of the second
state is answered by one or more of the first, or the first goes
wrong). It could move to `FlambdaSimulationProofs.v` if C0 wants it
there.

**What it does on the examples.** `FlambdaUnboxParamsExamplesSpec.v`
has the bodies of three of the functions of section 9, before and
after Simplify, written from what the tool prints, and a round that is
the round of the term before with the pass placed after
`follow_aliases` and before `drop_unused_params` (V4 agrees with the
place). The statements are computed:

- `pair_computed` and `int64_built`: after five such rounds the body
  before is the body after, up to bound names; after five rounds of
  today it is not; so the body after refines the body before, by the
  theorems of the passes and of the comparison;
- `pair_built`: after five rounds the body before has the parameters
  and the arguments of the body after and makes no block, but each arm
  of its `Switch` still goes through the continuation of its branch,
  whose handler is now one jump. `shortcut_switches` makes that
  shortcut only where the `Switch` is directly under the `Let_cont`;
  here a `Let` and another `Let_cont` stand between. V4 has a pass in
  review that forwards such an application wherever it is; with it
  this unit should validate too.

**What stops it**, beyond the above:

- only the `Let`s that the handler begins with are looked at, and
  only while each reads a box that is a parameter. A load that is
  first done inside a branch of the handler is left. Making it a
  parameter is right all the same when every application is known,
  but the new parameter then needs a name of its own (section 8);
- the new parameters are in the order of the `Let`s. Simplify's are in
  the reverse of the order of the fields. The two agree where the
  source reads the last field first, which is what the front end makes
  of a pattern and of `fst p + snd p`. Where they differ the
  validation fails; it never accepts more. Putting the leading loads
  of one parameter in a fixed order first would remove the
  dependence: a swap of two `Let`s that do not mention each other, an
  equivalence. Not built;
- the pass does not decide as Simplify does (depth, benefit). It fires
  where the handler begins by reading a parameter that every use
  builds; Simplify unboxes there too in every example measured.

**Renaming.** The functions compare names by equality and bind no name
that the term has not. `FlambdaUnboxParamsRenameSpec.v` has the
statements, proved: the pass commutes with a renaming
(`unbox_known_params_equivariant_statement`, which is
`FlambdaValidatorEquivarianceSpec.rewrite_equivariant` of the pass; and
the same with what is known renamed with the term), and it keeps scope
(`unbox_known_params_keeps_scope_statement`).

**Wiring.** This pass is not in `FlambdaValidateSpec.v`. The second
pass (section 7) validates the two bodies that this one validates and
the seven of variants, and is the one that the validation runs.

## 5. The first thing asked: subkinds

Where a use gives a block that the term does not show, Simplify binds
`Block_load` with the tag and the size of the decision just before the
application. `FlambdaPrimitiveSpec.eval_block_load` has no value on a
block whose tag or size is not the one the access kind gives. The
handler before reads the field with an access kind that names neither,
and perhaps on one path only.

So, in the model, under an environment in which that argument is a
block of another tag or size, or is no block at all, the term before
may run and the term after is undefined. The term after does not
refine the term before under all environments, and the bodies of code
are compared under all environments. No rewrite can close this: the
after side may not make a term more defined, and the before side may
not make one less defined.

What justifies the load in the compiler is the type of the argument,
and for an argument that is a parameter of the function, the result of
a call or the parameter of a recursive continuation, that type comes
from its subkind (`T.unknown_with_subkind`). The model has no subkinds
(`FlambdaModel.v`, "What is left out"). In every measured example in
which a use is not built in the term, the subkind is the only source:
`pair_join`, `pair_kept`, and the entry of every loop.

Asked of C2 and C0, and a decision for the human:

- binders carry subkinds, at least: tagged immediate, the boxed
  numbers, and a block of given tag whose fields have given subkinds
  (the compiler's `Variant`);
- binding a value that has not the subkind of its binder is undefined,
  as a mismatch of kinds is where it is executed. The compiler takes
  it so wherever it reads a subkind into a type.

With that, a before-side rewrite may give a load of a variable the tag
and the size that the subkind of its binder says (a refinement: where
they are wrong, the binding was undefined), and the hoisting of
section 3 with a `Let` at the use closes the case. Until then the
validation cannot accept a unit in which Simplify adds a field load at
a use, and should not.

This is not a wrong statement about any unit: run from empty
environments, a well-typed unit passes only values of the right shape.
It is a limit of what can be validated, and of every statement about
the body of code under all environments.

Numbers are not affected: `Unbox_number` at the use asks nothing more
than the same primitive in the handler. See section 8.

## 6. Loops, and the heap

**Loops** (agreed with V4). For a recursive continuation the same
rewrite is right: the applications inside the handler are applications
like the others, and the proof would be the same simulation. It is not
built, for two reasons. Simplify decides the unboxing of a loop
parameter from its subkind alone, never unboxes a variant there, and
the entry of the loop almost always gives a value that the term does
not show, with a load: section 5. And the pass leaves the handlers of
recursive continuations as they are, as `load_known_blocks` does;
`FlambdaRecHandlersSpec.rewrite_rec_handlers` takes it into them, for
the joins inside a loop.

V4 has one example that is not blocked by subkinds: a `bool ref` that
a `while` tests. The loop parameter is tagged before and a naked
immediate after, and every application gives a constant or the
parameter itself. It needs the pass extended to a recursive
continuation that is alone in its `Let_cont`, for `Untag_immediate`,
where an application inside the handler may give the parameter itself
(the new argument is then the new parameter). That is the next
extension; V4's pass for a parameter that every application gives the
same thing, which is in review, has the shape of the condition for a
loop.

**The heap** (confirmed by C4). The pass knows a block only through
`FlambdaBlockLoadSpec.known_blocks`: a variable bound to the model's
`Make_block`, which is immutable and gives a structural value, or a
symbol bound to a static block. A load of such a value reads no heap.
A block with an identity is made by another primitive today and is a
location, of which nothing is known, so the pass never fires on one.
When `Make_block` gains its mutability, `known_blocks` must keep to
`Immutable`; that is a change to `FlambdaBlockLoadSpec.v`, not to this
pass. Moving a load marked `Immutable` or `Immutable_unique` of a
location would need C4's statement that such a field is not written
again (`FlambdaHeapSpec.no_coeffects_statement`); nothing here does.

## 7. Variants and poison

What Simplify passes for a field of a constructor that the argument is
not is `poison`. The question was which statement is needed, of the
form "poison may be replaced by any value where it is not read
strictly", and whether it can be had before the human answers D26.

Such a statement is not what the validator needs. In the direction the
chain goes, a statement that poison is refined by any value would let
the term before lose a poison and the term after gain one. The term
before has none, and the term after has them. What is needed is to
introduce, on the term before, a new parameter that some applications
give a value which no run reads unless the term before is undefined.
Any constant would do for the proof; it must be `poison` only so that
the result is Simplify's term.

### What is built: `unbox_variant_params`

`FlambdaUnboxVariantsSpec.v`, with the proof in
`FlambdaUnboxVariantsProofs.v`. It is made as `unbox_known_params`
is, with three differences. It is not that pass and more: see "What
it does not cover".

1. The `Let` that reads a box need not be the first thing in the
   handler. It is the first one found going down the handler through
   the bodies of `Let`s and through the bodies, then the handlers, of
   non-recursive `Let_cont`s (`first_read`), provided that no binder
   on the way binds the parameter read or the variable of the `Let`,
   and that the variable is not free in the handler. The `Let` is
   removed where it is; its variable becomes the last parameter.
2. Where the `Let` is not the first thing in the handler, an
   application gets as its new argument
   (`extend_args_certain`), in this order: a constant of the kind of
   the `Let` in place of the read (`dummy_of`: `poison`, or 0 for
   `Get_tag` and `Untag_immediate`, which is what Simplify gives:
   `Unboxing_epa.compute_extra_args_for_variant`,
   `extra_arg_for_ctor`), if the term shows that the application does
   not come to the read (`never_reads`, below); a constant that the
   term shows the primitive to give, if it is of the kind of the
   `Let`; the field of a block that a `Let` in scope made, for a load
   at the kind of values; the number in a box that a `Let` in scope
   made, for the unboxing of such a box at the kind of the number, or
   the number that a `Let` in scope tagged, for the untagging
   (`made_number`); or, where the term shows that the primitive has no
   value on the argument for the parameter read, that constant
   again. The primitive is known to have no value
   (`no_value_on`) where it is a load or `Get_tag` of a constant, and
   where it is `Untag_immediate` of a variable that a `Let` in scope
   made a block, or of a symbol.

   An application does not come to a read (`never_reads`) where the
   constants it gives show it. The parameters that it gives a constant
   naked immediate are known: whether the value is an immediate and
   its tag, once those are parameters. In the handler every `Switch`
   on one of them is replaced by the arm it goes to (`take_arms`), and
   the continuations that nothing then applies are removed
   (`remove_unused_conts`); if what is left of the handler is, up to
   bound names (`expr_eqb`), what is left of the handler without the
   read, the read was in a continuation that this application does not
   reach. That is what a variant with several tags needs: the front
   end's load says nothing of the tag (`%block_load.[0]`), so it has a
   value on a block of another tag that has the field, and only the
   `Switch` on the tag keeps it from being read.

3. The reads are taken in an order (`next_read`): first a `Get_tag`,
   then an `Untag_immediate`, then an `Is_int`, then the loads and
   the unboxings, each sort from the top of the handler down. The new
   parameters are then in Simplify's order for a variant: the tag,
   the constant constructor, whether the value is an immediate, the
   fields (`Unboxing_epa.add_extra_params_and_args`).

So for `match v with None -> 0 | Some y -> y + 2` at a join of
`Some (x + 1)` and `None`: `Is_int` of the parameter is the first
thing in the handler and becomes a parameter by the first rule, as
before (0 from the block, 1 from the constant); the load of the field
is then the first thing in the handler of the continuation that the
arm 0 of the `Switch` applies, and becomes a parameter by the second:
the application that gives the block gives the field, and the one
that gives `None` gives `poison`.

The statement is `unbox_variant_params_refines_statement`:
`expr_refines e (unbox_variant_params e)`, under all environments,
with no premise.

### Why the constant may be given (the argument to attack)

The new parameter is read only below the place of the `Let` that was
removed: its variable was not free in the handler, so every use of it
was bound by that `Let`. In the term before, a run that comes to that
place evaluates the primitive on the parameter read, and that
parameter still has the value that the application gave, because no
binder on the way binds it. An application is given the constant in
two cases only.

- The term shows that the primitive has no value on what the
  application gives for the parameter read. A run of the term before
  that starts at such an application and comes to the place of the
  `Let` is undefined there, and a refinement asks nothing of the term
  after from then on; a run that does not come to that place never
  looks at the new parameter.
- The term shows that the application does not come to the read
  (`never_reads`). Then the handler and the handler without the read
  are equivalent under the constants that the application gives:
  each is equivalent to what is left of it, since taking the arm of a
  `Switch` on a variable that holds a known number and removing an
  unused continuation are equivalences, and the two that are left are
  the same up to bound names.

Nothing is said about what a primitive does with `poison`: the
constant could be any constant of the kind. D26 and T6-1 are about a
parameter that holds poison being read through what the types record
of it; here the claim is made of the term before, in which there is
no poison, and what it says of the term after is that the validator
has found Simplify's `poison` only at applications from which the
term before does not read, or would be undefined if it did. If
Simplify gave `poison` at a use from which the handler can read the
field, the two terms would differ at that argument and the unit would
not be validated.

The proof follows the argument and has no simulation of its own
(`take_arms` is proved by the lemmas of contexts; the removal of
unused continuations and the comparison are the validator's, with
their theorems). `FlambdaUnboxParamsProofs.read_refines`: under
variables that give
the new parameter a value `u` such that the primitive, whatever is
bound later, has on the parameter read the value `u` if it has one,
the handler without the `Let` refines the handler; by induction on
the way down to the `Let`, with the lemmas of contexts, and at the
`Let` itself either the primitive has no value (the term before is
undefined) or it has the value `u`, which the variable holds
already. The simulation of the first pass is then used as it is,
with that as its hypothesis about the two handlers
(`unbox_parameter_refines`).

Two things had to be got right, and are where to look.

- **Kinds.** Since the machine tests the kinds of the values that a
  handler is applied to, the new argument must be of the kind of the
  new parameter at every application, whether or not the run comes to
  the `Let`: otherwise the term after is undefined where the term
  before is not. For the first thing in a handler this takes care of
  itself (the `Let` tests the same value at once). Under a test it
  does not. So the constant is made of the kind of the `Let`
  (`dummy_of`); a constant that the term shows is taken only at that
  kind; a field is taken only of a block that `Make_block` made in
  scope, whose fields the primitive tested to be of the kind of
  values when it made the block (the proof carries that:
  `fields_valued`); and the content of a boxed number is taken only
  of a box that `Box_number` made in scope, which tested the number
  to be of the kind of the box (`numbers_kinded`). A field of a
  static block is not taken under a test, because nothing tests the
  kind of what a static block holds. It could be, with the same kind
  of fact carried for it.
- **Scope.** The new parameter is in scope in all of the handler, so
  its name must not be free there (`var_free_b`), and no binder
  between the top of the handler and the `Let` may bind it or the
  parameter read (`param_read`, `first_read`).

### What it does not cover

- **A read under a test that is not a `Switch` on a parameter given a
  constant.** `never_reads` knows only the parameters that the
  application gives a constant naked immediate, and replaces only a
  `Switch` on such a parameter. A read under a comparison, or under a
  `Switch` on what a `Let` of the handler computes of a parameter,
  is taken to be reachable; the application then needs an argument
  that is certain, or the pass stops.
- It stops at the first read, in its order, that cannot be made a
  parameter, even where the first pass would make the read at the
  head of the handler one. For a handler that begins with the load of
  a field of `x` and then reads the tag of `y`, where an application
  gives a known block for `x` and nothing known for `y`, the first
  pass makes the load a parameter and this one makes none, as the tag
  comes first in its order. The two bodies that the first pass
  validates are validated with this one
  (`earlier_examples_validated_statement`).
- Among the loads, the order of the new parameters is the order in
  which the handler has them, the body of a `Let_cont` before its
  handler. In the seven examples that is Simplify's (the front end
  reads the fields last to first, and puts the continuation of the
  first arm outermost).
- A field that the handler reads in two places becomes two
  parameters, where Simplify has one. A pass that makes one of two
  parameters that every application gives the same argument would
  mend it.
- The validation runs it in the first phase of the term before
  only (`FlambdaValidateSpec.normalise_expr_params`), once the
  values are followed and before the passes that bind or remove
  parameters. A join that is there only once a call is inlined is
  seen if the code that is inlined had it, since the first phase
  goes into code; `option_inlined` (section 9) is such a unit, and
  is stopped by something else. It makes no name.

### The other way

Copying the handler of a non-recursive continuation at each
application (inlining it where it is applied, with a wrapper
continuation at an arm of a `Switch`), on both terms, is an
equivalence and needs neither poison nor an analysis: in the copy for
a use that gives `None` the term before folds `Is_int` and the
`Switch` and never has the load, and the term after is left with an
unused parameter that goes. It would cover several tags. The cost is
the size of the normal form, which doubles at each join, and fresh
names for the wrappers. Not built.

### The tool

The conversion of the test tool refused a poison constant, so a unit
with an unboxed variant was "not checked". The model has the
constant and the conversion has the case: such a unit runs, and with
the pass in the validation it is validated (section 9).

## 8. What else is owed for pairs and numbers

- **A number that one use is given** (`int64_join`): Simplify binds
  `Unbox_number` at the use. That asks no more than the unboxing in
  the handler, so, unlike a field, it can be validated today. The
  rewrite must add a `Let` at the use. In an expression that is one
  `Let` before the application, of the variable of the handler's own
  `Let` (it must not be an argument of the application). At an arm of
  a `Switch` it needs a wrapper continuation, and so a fresh name:
  `FlambdaNameAbstractionSpec.fresh_name`, with the statement of
  renaming up to the new names that N2 and N3 have for
  `rename_apart`. The simulation is the one of this pass with one more
  case. Next after the renaming statements.
- **A load that is not at the head of the handler** (a record read in
  one branch only): `unbox_variant_params` does it, where what each
  application gives is certain to be of the kind of the load
  (section 7).
- **The order of the new parameters**, section 4.
- **A recursive continuation alone in its `Let_cont`**, section 6.

## 9. The examples

Each is one function that Simplify does not inline, called twice, so
that its code stays and is compared. `fst` and `snd` are
`%field0_immut` and `%field1_immut`; the arithmetic is declared as in
the other units from OCaml.

    (* pair_built *)
    let[@inline never] sum : bool -> int -> int =
     fun c x ->
      let p = if c then x, 1 else 2, x in
      fst p + snd p
    let result = sum true 3 + sum false 4

    (* pair_computed *)
    let[@inline never] sum : bool -> int -> int =
     fun c x ->
      let p = if c then x + 1, 1 else 2, x + 2 in
      fst p + snd p
    let result = sum true 3 + sum false 4

    (* pair_join *)
    let[@inline never] sum : bool -> int * int -> int =
     fun c pair ->
      let p = if c then 1, 2 else pair in
      fst p + snd p
    let result = sum true (3, 4) + sum false (5, 6)

    (* pair_kept *)
    let[@inline never] sum : bool -> int * int -> int * (int * int) =
     fun c pair ->
      let p = if c then 1, 2 else pair in
      fst p + snd p, p
    let result = fst (sum true (3, 4)) + fst (sum false (5, 6))

    (* int64_built *)
    let[@inline never] f : bool -> int64 -> int64 -> int64 =
     fun c a b ->
      let x = if c then add a b else sub a b in
      add x 1L
    let result = to_int (add (f true 3L 4L) (f false 5L 6L))

    (* int64_join *)
    let[@inline never] f : bool -> int64 -> int64 -> int64 =
     fun c a b ->
      let x = if c then add a b else b in
      add x 1L
    let result = to_int (add (f true 3L 4L) (f false 5L 6L))

    (* option_join *)
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let v = if c then Some (x + 1) else None in
      match v with None -> 0 | Some y -> y + 2
    let result = f true 3 + f false 4

    (* option_heap *)
    external on_heap : 'a -> 'a = "%identity"
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let v = if c then Some (x + 1) else None in
      match on_heap v with None -> 0 | Some y -> y + 2
    let result = f true 3 + f false 4

    (* list_heap *)
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let l = if c then [ x + 1 ] else [] in
      match on_heap l with [] -> x + 3 | y :: _ -> y + 2
    let result = f true 3 + f false 4

    (* shape_heap *)
    type shape = Empty | Full | Pair of int * int
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let v = if c then Pair (x + 1, x) else Full in
      match on_heap v with Empty -> 0 | Full -> 1 | Pair (a, b) -> a + b
    let result = f true 3 + f false 4

    (* shape2_heap *)
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let v = if c then Pair (x + 1, x) else Full in
      match on_heap v with
      | Empty -> 10 | Full -> x + 20 | Pair (a, b) -> a + b
    let result = f true 3 + f false 4

    (* nested_heap *)
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let v = if c then Some (x + 1, x) else None in
      match on_heap v with None -> 0 | Some (a, b) -> a + b
    let result = f true 3 + f false 4

    (* either_heap *)
    type either = Left of int | Right of int * int
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let v = if c then Left (x + 1) else Right (x, x + 2) in
      match on_heap v with Left y -> y + 3 | Right (y, z) -> y + z
    let result = f true 3 + f false 4

    (* int64_option_heap *)
    let[@inline never] f : bool -> int64 -> int64 =
     fun c x ->
      let v = if c then Some (add x 1L) else None in
      match on_heap v with None -> 0L | Some y -> add y 2L
    let result = to_int (add (f true 3L) (f false 4L))

    (* pair_loop *)
    let rec fib : int -> int * int -> int =
     fun n acc ->
      if n = 0 then fst acc else fib (n - 1) (snd acc, fst acc + snd acc)
    let result = fib 10 (0, 1)

    (* result_join *)
    type outcome = Done of int | Failed of int
    let[@inline never] f : bool -> int -> int =
     fun c x ->
      let v = if c then Done (x + 1) else Failed x in
      match v with Done y -> y + 2 | Failed e -> 0 - e
    let result = f true 3 + f false 4

    (* option_inlined *)
    external opaque : 'a -> 'a = "%opaque"
    let[@inline] f : bool -> int -> int =
     fun c x ->
      let v = if c then Some (x + 1) else None in
      match v with None -> 0 | Some y -> y + 2
    let result = f (opaque true) 3

The sources are in `middle_end/flambda2/tests/semantics/ocaml/`, but
for `int64_join` as it is written here (the unit of that name there
calls `f` once, so the call is inlined, and is validated). Measured
with the test tool, built without the line that runs
`unbox_variant_params` in the validation and with it (the validation
and the units as they were before the lifting out of the arms of a
test was added); steps are those of the machine before and after
Simplify. In every unit the two runs
give the same result.

| Source | What Simplify unboxes | Steps | Without the pass | With it |
|--------|-----------------------|-------|------------------|---------|
| `pair_computed` | the pair of the join, computed on both paths; no block is left | 45, 29 | not validated | validated |
| `int64_built` | the boxed number of the join, boxed on both paths | 61, 43 | not validated | validated |
| `pair_built` | as `pair_computed`, each branch left with a jump only, which Simplify shortcuts | 43, 21 | not validated | validated |
| `int64_join` | the same, one path gives a parameter of the function: an unboxing is added at that use | 51, 41 | not validated | not validated: a `Let` at the use, with a wrapper at the arm, section 8 |
| `pair_join` | the pair, one path gives a parameter of the function: two loads with tag and size are added at that use | 31, 28 | not validated | not validated: subkinds, section 5 |
| `pair_kept` | as `pair_join`, the pair staying a parameter beside its fields | 35, 33 | not validated | not validated: subkinds |
| `pair_loop` | the accumulator of the loop; the entry loads the fields of the function's parameter | 192, 85 | not validated | not validated: subkinds; loops |
| `option_join` | the option, allocated in a region: `is_int` and the field, `poison` for the field where the use gives `None` | 55, 29 | not validated | validated |
| `option_heap` | the same, the option on the heap | 47, 29 | not validated | validated |
| `list_heap` | the list: `is_int` and the head, `poison` for the head where the use gives `[]` | 54, 33 | not validated | validated |
| `shape_heap` | two constant constructors and a pair: `is_int` and the two fields, `poison` for both where the use gives a constant constructor; the value stays a parameter | 54, 30 | not validated | validated |
| `shape2_heap` | the same with the two constant constructors told apart: the constant constructor, `is_int` and the two fields; 0 for the constant constructor where the use gives the pair | 61, 36 | not validated | validated |
| `nested_heap` | an option of a pair: `is_int` and the two fields of the pair, `poison` for both where the use gives `None` | 50, 29 | not validated | validated |
| `either_heap` | two constructors that hold fields: the tag and the fields of both, `poison` for the fields of the constructor that the use does not give | 58, 37 | not validated | validated |
| `int64_option_heap` | an option of a boxed number: `is_int` and the number unboxed, `poison` of the kind of the number where the use gives `None`; nothing is boxed on the way | 63, 38 | not validated | validated |
| `result_join` | two constructors that hold a field, in a region: the tag and the field of each, `poison` for the field of the other | 64, 33 | not validated | validated |
| `option_inlined` | the option of a function that is inlined where its condition is not known: `is_int` and the field, in the unit itself | 36, 12 | not validated | not validated: the pass unboxes the join; an arm of the term before then applies a continuation whose handler is one jump, which the second phase of the validation does not forward |

Over all the units of that directory that were there before the last
four, the line changes nine verdicts, those of the table, and nothing
else in the output of any unit; over the units written by hand it
changes none; of the 600 of `census/README.md` two more are validated
(`c_functions_0055`, `c_unknown_scalar_0122`) and nothing else
changes. `pair_built` needed,
besides the pass, the forwarding of an arm through a continuation
bound above a `Let`, which the first phase has
(`forward_applications`).

## 10. Asked of others

- **C2, C0, the human**: subkinds on binders, and a mismatch at a
  binder undefined (section 5). Recommended. Without it the unboxing of
  a block that is not built in the term cannot be validated, in a loop
  or out of one.
- **V2**: to check the line for `unbox_variant_params` in the first
  phase of the term before, which T6 wrote when the orchestrator
  asked, with the units it turns, and to regenerate the tables of the
  README of the units from OCaml. The line is after `follow_aliases`,
  the following of aliases in loops, the loads of known blocks and
  the unboxing of known numbers, and before the passes that bind or
  remove parameters. It uses `unbox_variant_params_refines`
  (`FlambdaUnboxVariantsProofs.v`) and the two facts of renaming and
  of scope (`FlambdaUnboxParamsNamesProofs.v`). `unbox_known_params`
  has the same three and is not run: the second pass validates the
  two bodies that it validates
  (`earlier_examples_validated_statement`). The sources that wait for
  subkinds are validated by neither.
- **V4, V2**: `option_inlined`. Whether the second phase of the term
  before may forward an application through a handler that is one
  jump, as the first does.
- **V4**: nothing more; the place in the round is agreed.
- **N1, N3**: nothing yet. The `Let` at a use under a `Switch`
  (section 8) and the copy of a handler (section 7) will need a fresh
  continuation name each.
- **C0**: whether `ahead_refines` should live in
  `FlambdaSimulationProofs.v`.
- **The compiler's developers**: `unboxing_epa.ml` refers to
  `doc/unboxing.md`, which is not in the tree.
