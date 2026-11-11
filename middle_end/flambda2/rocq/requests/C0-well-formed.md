# C0: one definition of a well-formed term. A proposal

Owner: C0. For the human. Nothing is restructured by this note: it
says what the definition would be, what it would come with, in what
order, and what is asked of C1, C2, C3 and N1.

The compiler has no single definition of a well-formed Flambda 2 term.
This work is to end with one: `FlambdaWellFormedSpec.well_formed_unit`.
A condition on terms that a stream finds goes there and not into a
premise of that stream's statements; and a term that the compiler
cannot build, or fails on, and that the model accepts, is first a hole
in that definition.

## 1. Two layers, kept apart

- **Well-formed** (`well_formed_unit`): true of every unit the compiler
  builds, GADTs and layout `any` included. A statement may take it as
  a premise. A unit made by the compiler that fails it is a finding:
  the condition is too strict, or the compiler is wrong.
- **Agreement of kinds.** Real units have mismatches of kinds, so
  "kinds agree wherever they meet" is never a premise of a statement
  about the compiler's terms; such a mismatch is undefined where it is
  executed, and that is the machine's business. C2's check
  (`well_kinded_unit`, in its own file) is not that strict property,
  which is defined nowhere. After the human's rulings it asks only for
  the agreements on which the compiler stops whatever the flags. C2
  proposes it as a condition of well-formedness; section 7 has the
  question.

The test for which layer a condition belongs to: can a unit that the
compiler builds with its default flags break it, in a branch that
never runs? If so it is not well-formedness.

## 2. The conditions of well-formedness

"Where the compiler establishes it" is one of: a **type** that cannot
express the bad term; a **creation function** that checks; a **pass**
that stops when it meets the bad term, whatever the flags; an
**invariant check** that runs only with `-flambda2-invariants`; or
**nothing**. A row that says nothing, or only an invariant check, is
an unchecked assumption of the compiler, and has an entry in the
record of discrepancies.

| | Condition | Owner | Where the compiler establishes it |
|-|-----------|-------|-----------------------------------|
| 1 | Static bindings are at toplevel | C0; there today | Pass: `simplify_named.ml`, the case `Static_consts`, for a group that binds a symbol. A group of code only may be anywhere; the model refuses it (C0-3). What toplevel is has no one statement (`Downwards_env.at_unit_toplevel`, set and cleared in `simplify_let_cont_expr.ml`) |
| 2 | A symbol or code id is bound once in the unit | C0; there today | Nothing, across the unit (C0-4). Within one group: invariant check (`Bound_static.create`). Within one handler: pass (`Flow_acc.record_symbol_binding`). `Typing_env.add_symbol_definition` has a note that redefinition is not checked |
| 3 | Every variable and continuation used is in scope | C0, by N1's free names; in C2's checker today | Pass: `Typing_env` ("Variable ... not bound"), `Upwards_env.find_continuation`, when Simplify reaches the use; and the end of `simplify.ml` for the unit. No creation function |
| 4 | Every symbol mentioned is bound (the human, D8); every code id mentioned is bound or deleted | C0 | Pass: `Typing_env` ("Symbol ... not bound"), for a symbol of the current unit; one of another unit comes from its `.cmx`. Code ids: `To_cmm_env` |
| 5 | The names of one binder are distinct: parameters of a handler; those of code, with `my_closure`; continuations of a recursive group; the two continuations of code | C0, by N1's rules; C2's checker has the first two | Continuations of a group: creation function (`Bound_continuations.create`). Parameters: invariant check only (`Bound_parameters.create`, `Bound_for_function.create`). The two continuations of code: nothing found |
| 6 | Code is closed: no free variable but its parameters and `my_closure`, no free continuation but its two | C0, by N1's free names; today a premise of `FlambdaApplySpec.inlinable` | Creation function (`Code0.create`), but of the free names its caller supplies, not of ones it computes (C0-5) |
| 7a | A closure is at a function slot of its set | C3 | Type: one pattern binds a variable for each function slot (`Bound_pattern.Set_of_closures`) |
| 7b | The function slots of a set are distinct | C3 | Nothing: they are an association list whose invariant function has no caller (C3-5) |
| 7c | The functions of a set have each their own code id (the human, D28) | C3 | Nothing; Simplify stops later with "code_id has been bound twice" (R2-7) |
| 7d | A group binds a static set whole, each symbol at its slot (D4, option (a)) | C3 | Type (one pattern binds the set) and creation function (`Static_const.match_against_bound_static_pattern`, slots in order) |
| 8 | The tag of every block made, by `Make_block` or statically, and the tag a `Block_load` names, is in `[0, 251)` (the human, D23). Proposed with it: a constant is in the range of its kind (D13) | C1 | Type (`Tag.Scannable.t`, whose creation function refuses others). Constants: type, I believe (`Reg_width_const`, not read); the fexpr parser wraps `int8` and `int16` (C1-11) |
| 9 | Annotations are there and of the right length: as many kinds as parameters; as many arguments of a call as its own arity; as many arguments of an `Apply_cont` as the continuation has parameters | C2, the part of its check that is not agreement of kinds | Type: a parameter carries its kind (`Bound_parameter`). `Apply_cont`: pass (`Continuation_uses.add_use`). `Apply`: nothing by design; `simplify_apply_expr.ml` walks the two lists together and raises if they differ |

I read the compiler's files for rows 1 to 6, 7a, 7d, 9 and the tags;
7b and 7c are as C3 and R2 report them.

From the types (T1, T2): nothing is asked of terms so far. T1 uses
`run_extends_statics`, which is a statement of this file, and its own
conditions are on types (below).

Known, and not sayable in the model yet. The header would list them,
so that the gaps show:

- exception handlers: never recursive (`Let_cont.create_recursive`
  checks), their arity, and trap actions, which a comment in
  `flambda.ml` says are not checked. With C5;
- a symbol or code id of another unit; that a unit binds its module
  symbol. The model has one unit;
- a new version of code and the code it replaces (C0-1). With S4;
- distinct value slots of a set and distinct arms of a `Switch`. The
  compiler's are maps (type); the model's are lists, and the first
  wins. A condition, or left so: small either way.

Not well-formedness, and kept out:

- agreement of kinds (section 1), and everything else that is
  undefined only when executed;
- what holds only after Simplify (no `Switch` on a constant, no
  over-application of a direct call);
- conditions on types and typing environments. I ask T1 to lay its
  predicate on raw type structures out in the same way in the types
  library, under a name that says "type"; the header here points at it;
- freshness of bound names. In the compiler a binder is a name
  abstraction and opening it gives fresh names; N1's pilot is how the
  model gets the same. Row 5 is what is left of it on raw terms.

## 3. The shape of the definition

All of it is in `FlambdaWellFormedSpec.v` (C0's): the header, which is
the table and the three lists above; each check, a boolean function of
the term that uses nothing of the machine; and their conjunction.

    Record unit_interface := {
      unit_return : continuation;
      unit_exn : continuation
    }.

    Definition well_formed_unit (u : unit_interface) (e : expr) : bool :=
      statics_at_toplevel u e          (* 1 *)
      && static_names_bound_once e     (* 2 *)
      && names_in_scope u e            (* 3 *)
      && statics_in_scope e            (* 4 *)
      && binders_distinct e            (* 5 *)
      && code_closed e                 (* 6 *)
      && sets_well_formed e            (* 7 *)
      && tags_in_range e               (* 8 *)
      && annotations_well_formed u e.  (* 9 *)

The record stands for `Flambda_unit.t`: a later field (the kinds of
the value slots for C2, the module symbol) then changes no call.
Today the check takes the exception continuation alone.

A stream writes its check and I apply it at its merge, with its row of
the header; a reviewer reads the row against the compiler. What a
stream proves about its condition may stay in its own files.

Row 4 needs care in one place, which the header will state: a symbol
bound at toplevel is in scope in what follows it and also in the
handler of an enclosing toplevel continuation, since that handler runs
after the body. Simplify makes such terms: a constant lifted while the
body is simplified is known in the handler and placed in the body
(`simplify_let_cont_expr.ml`, `consts_lifted_after_fork`). Row 1
already has the definition of such handlers. C1 has proposed this row
too, and has made every primitive have no value on a symbol that is
not bound, with a law that says so; that change is with its reviewer.

## 4. The theorems

In `FlambdaWellFormedSpec.v`, proved in its `Proofs` file from what
each stream proves:

- `well_formed_state : state -> Prop`, a definition to be reviewed:
  what a run keeps. One part for each row that says something of a
  run. (For rows 1 and 2 it exists, as `inv` in the `Proofs` file; it
  moves to the `Spec` file.)
- A unit that passes starts in a well-formed state, and **a step keeps
  a state well-formed**.
- **A well-formed state does none of the things the conditions are
  there to exclude**, each a test on a state:
  - it does not read a variable, continuation, symbol or code id that
    is not bound (rows 3 and 4; this is the theorem asked for with
    D8);
  - it does not bind a static name twice, call code whose body binds
    one, or define a recursive handler that does (rows 1 and 2;
    today's `static_fault`);
  - it does not make a closure at a slot its set has not got, and
    every static set in it is bound whole (row 7; C3 has both proved);
  - it does not make a block with a tag out of range (row 8).
- So no state of the run of a well-formed unit does any of them:
  today's `well_formed_never_faults_statement`, widened.

Each condition also comes with a unit of the examples that passes and
a term that fails, kept as a statement that shows what then goes wrong
(C3's `partial_static_set_statement` is the pattern). Rows 5 and 6
exclude nothing at run time; each names instead one proved statement
that is false without it.

Later, and I think worth having: every way a step can be undefined is
either one of the tests above or is on one list, written as a function
of the state (`Invalid`; a primitive with no value; a `Switch` with no
arm; a call of what is not a closure, of other code, at other
arities; a projection at the wrong slot). That list would be the
model's whole account of undefined behaviour in one definition, where
today it is spread over the machine, and it is where the `CR`s on
undefined cases would sit together.

## 5. Rules for the streams

- No `Spec` file keeps a condition on terms as its own premise if the
  compiler's terms always satisfy it. It is proposed as a row, with
  the place in the compiler, or "nothing".
- Agreement of kinds is never such a premise. C2's statements about
  well-kinded units take `well_kinded_unit` as their own premise;
  nothing else does until the question of section 7 is answered.
- Scope and free names are computed by one function, N1's. There are
  four today (`expr_in_scope`, `free_continuations`, the relations of
  `FlambdaNominalSpec.v`, C2's check); rows 3 and 6 are not a fifth.
- The test tool says which condition failed. A unit that fails before
  Simplify is reported and counted, never passed over; one that fails
  after is an error, as now.
- A function on terms that models something Simplify does owes three
  things: it refines, it commutes with renaming (N1), and it keeps
  `well_formed_unit`. The third is asked of the S streams when they
  start, not of the validator's own normalisations now.
- `validate_unit_sound` keeps its statement: no premise is added.

## 6. Order, and what it costs

1. Mine, between two epochs, one reviewer, about a day: the header as
   the table; the record; the two checks there today under the names
   above; `well_formed_state` and "a step keeps it" stated for them.
   No file moves and the tool changes by one line.
2. With C3's epoch: row 7, as its request already has it.
3. After C3's epoch, mine, about two days: row 4 with its theorem.
   Symbols are not names that a binder renames, so it does not wait
   for N1; it does wait for C3, which changes what mentions a symbol.
4. With C1, a leaf: row 8. With C2's first step: row 9.
5. Rows 3, 5 and 6 when N1's pilot is judged, since they are to use
   its free names.

## 7. For the human

- **Row 1 is stricter than the compiler** (C0-3). Keep it so (my
  recommendation, until an example needs otherwise: the machine makes
  a call of code that binds anything static undefined), or follow the
  compiler and allow a group of code alone anywhere.
- **Is C2's check a condition of well-formedness?** It asks for the
  agreements of kinds on which the compiler stops whatever the flags:
  a `Let` against what it binds
  (`Typing_env.add_variable_definition`), the arguments of an
  `Apply_cont` against the parameters (`Continuation_uses.add_use`),
  the scrutinee of a `Switch`, the return continuation of a call
  against the call's return arity, a value slot and a field of a
  static block against what they hold. What the compiler tolerates,
  the check lets through. C2's position: every unit the compiler
  builds therefore passes, so by the test of section 1 it is a tenth
  row. Mine: not yet. That the compiler stops on a mismatch is
  evidence about the code Simplify reaches; a unit as closure
  conversion builds it could hold one in code that Simplify drops
  first, and the evidence so far is hand-written programs. I recommend
  it stays beside `well_formed_unit`, run by the tool and reported
  separately, until C2 has argued from closure conversion that such
  terms are not built, or a corpus of real units has been through it;
  then it is one line to add.
- **Constants in range** (D13) as part of row 8, like the tags.
- **The classification of undefined behaviour**: wanted or not. It
  changes no existing statement; perhaps two days once C1, C2 and C3
  are in.
