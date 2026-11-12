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
- Variants need no statement about poison and no answer on D26, but
  they need either a rewrite that knows which arm of a `Switch` a load
  is under, or the handler copied at each application. Neither is
  built. The tool does not convert a poison constant yet, so no such
  unit is checked today (section 7).

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
equivalence because `load_known_named` gives the field of a known
block where the access kind agrees with the block, and the load in the
handler may still have no value on it (a field kind that asks for an
immediate; `FlambdaBlockLoadSpec.v` says the same of its own pass).

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
that the term has not. The statement that the pass commutes with a
renaming, and that it keeps scope, is owed in
`FlambdaUnboxParamsRenameSpec.v` (next commit), in the form of
`FlambdaValidatorEquivarianceSpec.rewrite_equivariant`.

**Wiring.** The pass is not in `FlambdaValidateSpec.v`. V4 is
rewriting that part of the round and will add the line, given the
statement and the lemma of renaming.

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
give a value nobody reads. Any constant would do for the proof; it
must be `poison` only so that the result is Simplify's term.

The statement that is needed is this. Let `k` have a parameter `x` and
a parameter `t` that every application gives the tag of what it gives
for `x` (after `unbox_known_params`, `t` is the parameter made of
`Get_tag x`; likewise for `is_int`). A load of field `j` of `x` in the
handler, at a place that is reached only through the arm for the tag
`T` of a `Switch` on `t`, may become a parameter, given at each
application the field `j` of its argument where that is known to be a
block of tag `T`, and any simple that has a value where the argument
is known to be an immediate or a block of another tag. The result
refines the term, under all environments.

It needs no premise about poison, and no answer on D26: on the runs
where the parameter holds poison the handler does not reach the place
where it is used, so what a primitive does with a poison value is
never asked. (If D26 is answered so that reading poison is undefined
everywhere, the statement is unchanged.) What it needs is the
condition "reached only through that arm", which is about the control
flow of the handler: the load is in the handler of another
continuation, which only that arm applies. That is a second analysis
and a harder simulation, and it is not built. The first step of it is:
`Is_int` and `Get_tag` at the head of the handler do become parameters
by the pass that is built.

There is a second way, which needs no analysis and no poison either:
copy the handler of a non-recursive continuation at each application
(inlining it where it is applied, with a wrapper continuation at an
arm of a `Switch`), on both terms. It is an equivalence. In the copy
for a use that gives `None`, the term before folds `Is_int` and the
`Switch` and never has the load; the term after folds the `Switch` on
the constant `is_int`, and the parameter that holds `poison` is left
unused and goes. The two copies are then the same. The cost is the
size of the normal form, which doubles at each join; it would need a
bound. It needs fresh names for the wrappers.

Decided: stop at pairs and numbers, as asked. Of the two ways, the
second is the one to try first when variants are wanted: it is one
rewrite with a simple statement, and it also covers a closure with a
single entry.

One thing blocks every unit with an unboxed variant before any of
this: the conversion of the test tool refuses a poison constant, so
such a unit is "not checked". The model has the constant. V2 is adding
the case.

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
  one branch only). Right where every application is known, as a
  refinement; the new parameter needs a name of its own, or the load
  must first be moved to the head, which is only right where the
  parameter is known to be a block at every use.
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

    (* pair_loop *)
    let rec fib : int -> int * int -> int =
     fun n acc ->
      if n = 0 then fst acc else fib (n - 1) (snd acc, fst acc + snd acc)
    let result = fib 10 (0, 1)

Measured with V2's trial tool (the validation of the integration
branch with V2's and V4's series that were pending on 2026-11-12);
steps are those of the machine before and after Simplify. V2 is adding
the sources to `middle_end/flambda2/tests/semantics/ocaml/`.

| Source | What Simplify unboxes | Steps | Today | What it needs |
|--------|-----------------------|-------|-------|---------------|
| `pair_computed` | the pair of the join, computed on both paths; no block is left | 45, 29 | the same, not validated | `unbox_known_params`: with it the body in Rocq is validated |
| `int64_built` | the boxed number of the join, boxed on both paths | 61, 43 | the same, not validated | `unbox_known_params`: likewise |
| `pair_built` | as `pair_computed`, each branch left with a jump only, which Simplify shortcuts | 43, 21 | the same, not validated | `unbox_known_params`, and the forwarding of an arm through a continuation bound above a `Let` (V4's, in review) |
| `int64_join` | the same, one path gives a parameter of the function: an unboxing is added at that use | 51, 41 | the same, not validated | a `Let` at the use, with a wrapper at the arm: section 8 |
| `pair_join` | the pair, one path gives a parameter of the function: two loads with tag and size are added at that use | 31, 28 | the same, not validated | subkinds: section 5 |
| `pair_kept` | as `pair_join`, the pair staying a parameter beside its fields | 35, 33 | the same, not validated | subkinds |
| `pair_loop` | the accumulator of the loop; the entry loads the fields of the function's parameter | 192, 85 | the same, not validated | subkinds; loops |
| `option_join` | the option: `is_int` and the field, `poison` for the field where the use gives `None` | | not checked: the conversion refuses the poison constant | the conversion; then section 7 |

Of V2's 172 sources, two unbox a pair and both validate already,
because the pair is known on every path and the join is inlined away;
fifteen have a loop over a `ref` (V4's). None is stopped by a join
whose parameter was unboxed, so these eight are new coverage.

## 10. Asked of others

- **C2, C0, the human**: subkinds on binders, and a mismatch at a
  binder undefined (section 5). Recommended. Without it the unboxing of
  a block that is not built in the term cannot be validated, in a loop
  or out of one.
- **V4** (or the owner of the validator's wiring): the line for
  `unbox_known_params` in the round of the term before, after
  `follow_aliases` and before `drop_unused_params`.
- **V2**: the conversion of the poison constant; the sources above.
- **N1, N3**: nothing yet. The `Let` at a use under a `Switch`
  (section 8) and the copy of a handler (section 7) will need a fresh
  continuation name each.
- **C0**: whether `ahead_refines` should live in
  `FlambdaSimulationProofs.v`.
- **The compiler's developers**: `unboxing_epa.ml` refers to
  `doc/unboxing.md`, which is not in the tree.
