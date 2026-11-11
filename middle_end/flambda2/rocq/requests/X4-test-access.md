# X4: reading the compiler's types from tests

Owner: X4. For the human. Branch `flambda2-rocq/X4-test-access`.

T7's differential tests convert the compiler's types to the Rocq
model's and compare. They asked for three changes to production
interfaces (decision D33). The answer was: accessors for the block
size; no type equality for `Flambda2_types.t` ("it would break
abstraction. Maybe there is another way?"); a hook in Simplify is fine.

**Decided overnight, 2026-11-11, in the human's absence and for his
review (decision D33):** the recommended options go ahead, option R of
section 2 with the hook of section 3, and N1 of section 3.2. Each is a
commit of its own with a test and can be reverted alone; each new entry
point has a `CR mshinwell` saying that it is for tests and was decided
so. The four questions of section 6 are what he is asked to confirm or
overturn.

This note says what was done for the first, and proposes one small
mechanism for the other two together. Sections 3 and 4 are the
proposal; section 2 has the alternatives. Nothing of sections 2 to 4
is merged. The recommended options are built on the branch, each as a
commit of its own with a test, so that the design could be checked and
so that a commit can be dropped if its option is refused: after the
commit for the accessors come `flambda2: Let tests observe the typing
environments of Simplify` (option R with the hook of section 3) and
the commit for N1 of section 3.2. Section 7 says what building them
showed.

## 0. In short

- **Done, its own commit:** `Type_grammar.Block_size.of_target_ocaml_int`
  and `to_target_ocaml_int`. The type stays abstract.
- **Proposed (option R):** an observer inside the types library. A
  test registers a function through the library's *internal*
  interface and is given the internal typing environment; the *public*
  interface gains one function, which mentions no internal type and
  does nothing unless an observer is registered. Simplify calls it at
  two places: the start of each continuation handler, and the end of
  the unit. Production change: 10 lines of code in two files of the
  types library, one declaration in its public interface, and two
  lines in Simplify.
- **Found on the way, and needed for request 3 only:** a test cannot
  match the names of those environments with the names of the output
  term, because every opening of a binder freshens the bound names and
  the terms export no opening that does not. Section 3.2 has three ways
  across; the recommended one exports, for the five binding constructs
  of `flambda.mli`, the opening that the printer already uses. T7 has
  checked the finding and asks for that one. The observer does not
  depend on it: all that T7 does with types from compilations, short
  of comparing them with runs, needs the observer only.
- **Asked of the human:** the four questions of section 6.

## 1. What the tests need (agreed with T7)

1. To read, as `Type_grammar.t`, the types that Simplify computes.
   They are all reached through typing environments; no test needs to
   convert a bare `Flambda2_types.t`.
2. For the comparison of types with a run of the Rocq machine (part 3
   of the tests), first version: the environment at the entry of each
   continuation handler (parameters, and what is in scope), and the
   final environment of the unit (symbols). "After each `Let`" is not
   needed yet.
3. Identification: the continuation whose handler is entered. The test
   runs Simplify in its own process (`Flambda2.flambda_to_flambda` on a
   parsed `.fl` file, as `tests/tools/flsemantics.ml` does), so it has
   the output term of the same run and matches continuations and
   variables by identity. The hook need not hand over the term.
4. The call must not change what Simplify does.
5. For the standard library, the types in its `.cmx` files, as
   `Type_grammar.t`.

What a test can do today, with no change: the library is a wrapped
dune library, so its modules are visible outside it under the names
the build gives them (`Flambda2_types__Type_grammar`,
`Flambda2_types__Typing_env`, ...). T7's converter uses them. Nothing
else in the tree does (`rg Flambda2_types__` finds no use), and
nothing in a dune file forbids it. So a test can already build and
take apart *internal* types and environments. What it cannot do is
connect them with the *public* abstract ones that Simplify holds:
`Flambda2_types.t` and `Flambda2_types.Typing_env.t` are declared
abstract in `flambda2_types.mli`, so the type checker does not know
that they are the internal types.

## 2. Options for reading the types (request 1)

"Client" below means code outside the library. "Cost" is what a
compilation pays when no test is involved.

| | Option | Lines in production interfaces | What a client can newly do | Cost | Compiler touched |
|-|--------|-------------------------------|----------------------------|------|------------------|
| R | Observer registered inside the library (recommended) | Public: 1 function, no internal type. Internal: 1 function | Through the public interface: call a function that does nothing. Only a client that names an internal module (`Flambda2_types__Typing_env`) can register, and then reads the environments that are reported | A call, a load and a branch at each place Simplify reports | 2 files of the types library (10 lines of code) and 1 declaration in its public interface; 2 lines in Simplify |
| S | `For_testing` submodule of the public interface, with functions that return the internal types | Public: 2 functions whose results are internal types | Any client turns any `t` or `Typing_env.t` into its representation, by a function of the public interface | None for the conversion. The hook of section 3 is still needed, as a reference in Simplify: the same call, load and branch | 2 files of the types library (about 9 lines), and about 10 lines in Simplify for its own hook |
| X | Read the types from `.cmx` files | None | Nothing | None | Nothing. But see below: it needs a cast in another form, and does not give the types of variables |
| P | Print the types and parse them in the test | None for the types | Nothing | The hook only, as for S | The hook in Simplify; and changes to the printer, see below |
| E | The type equalities (what T7 first asked) | Public: 2 lines, `type t = Type_grammar.t` and `type typing_env = Typing_env.t` | Every client sees the representation, and the type checker uses it everywhere | None | 1 file |
| U | An unsafe cast in the test | None | Nothing | None | Nothing. Unsound the day the public type is no longer the internal one (the type checker would not notice) |

### R: an observer registered inside the library

`types/env/typing_env.mli` (internal; `flambda2_types.mli` does not
export `For_testing`):

```ocaml
module For_testing : sig
  (** [set_observer (Some f)] makes [notify_test_observer t ~at_handler]
      call [f t at_handler]. [set_observer None], which is the initial
      state, makes it do nothing. [f] must not raise and must only
      read. *)
  val set_observer : (t -> Continuation.t -> unit) option -> unit
end

val notify_test_observer : t -> at_handler:Continuation.t -> unit
```

(The comments in the tree say more, at the reviewer's request: the
final environment of a unit is reported under its return continuation,
and a report need not be a handler of the term that Simplify returns.)

`types/env/typing_env.ml`:

```ocaml
let test_observer : (t -> Continuation.t -> unit) option ref = ref None

module For_testing = struct
  let set_observer observer = test_observer := observer
end

let notify_test_observer t ~at_handler =
  match !test_observer with
  | None -> ()
  | Some observer -> observer t at_handler
```

`types/flambda2_types.mli`, in `module Typing_env : sig ... end` (the
only public line; `flambda2_types.ml` needs no change, it includes the
internal module):

```ocaml
  (** For tests of the type system: report that [t] is the environment
      at the start of the handler of [at_handler]. Does nothing unless a
      test has registered an observer, which can only be done through
      the internal interface of this library. *)
  val notify_test_observer : t -> at_handler:Continuation.t -> unit
```

A test:

```ocaml
module TE = Flambda2_types__Typing_env
module TG = Flambda2_types__Type_grammar

let seen = ref []
let observe env k = seen := (k, env) :: !seen
let () = TE.For_testing.set_observer (Some observe)
(* ... run Simplify ...; then, for a variable [x] of the output term: *)
let ty : TG.t = TE.find env (Name.var x) None
```

Why it keeps the abstraction: the public signature does not mention
`Type_grammar` or the internal `Typing_env`. A client that keeps to
the public interface learns nothing about the representation, in the
type checker or at run time. The only way in is to name
`Flambda2_types__Typing_env`, which is outside the public interface by
construction, was already possible, and can be found by `rg` (and
could be ruled out for production code by a line in a check, if
wanted).

It also covers request 5 with no further change: a test builds a
*public* environment whose resolver gives the `Serializable.t` read
from a `.cmx` file (`Flambda_cmx_format.import_typing_env_and_code`),
calls `notify_test_observer` on it itself, and its observer receives
the internal environment; `find` on a symbol of that unit then goes
through the resolver and returns a `Type_grammar.t`.
`Typing_env.Serializable.ids_for_export`, which is public, lists the
names.

A variant with the same public line: the reference and the two
functions in a new internal module of their own instead of
`typing_env.ml` (two new files, one line in `flambda2_types.ml`).

A variant with no public line at all was looked at and is not
proposed: call the observer from inside the library, in
`cut_and_n_way_join` and in `Typing_env.Pre_serializable.create`.
Simplify does not call the join for a handler with a single
non-recursive use, nor for the handlers of a recursive group
(`simplify/join_points.ml`, `simplify_let_cont_expr.ml`), the join is
not told which continuation it is for, and `Pre_serializable.create`
is not called with `-opaque` and comes after the reaper. It would tie
the tests to accidents of how Simplify uses the library.

### S: a `For_testing` submodule that returns the internal types

`types/flambda2_types.mli`:

```ocaml
module For_testing : sig
  val type_grammar : t -> Type_grammar.t

  val typing_env : typing_env -> Flambda2_types__Typing_env.t
end
```

`types/flambda2_types.ml`:

```ocaml
module For_testing = struct
  let type_grammar t = t

  let typing_env t = t
end
```

(The second result type has to be written with the build's name:
at that point of the interface `Typing_env` is the public module. This
option was not built.)

The tree has `For_testing` submodules elsewhere (`backend/reg.mli`,
`utils/load_path.mli`, `backend/regalloc/*.mli`); Flambda 2 has none.
The types stay abstract for the type checker, so no client depends on
the representation by accident. But the way to the representation is
now in the public interface: any client can write
`Flambda2_types.For_testing.type_grammar ty` and match on the result,
and only the name says it should not. The hook of section 3 would be
separate: a reference in a module of Simplify, with a public type
(`Flambda2_types.Typing_env.t -> Continuation.t -> unit`).

### X: the types exported to the `.cmx` file

`Flambda_cmx_format.import_typing_env_and_code` gives a
`Flambda2_types.Typing_env.Serializable.t`, which is abstract too. A
test can only read it at the internal type by unmarshalling the
section itself at a type of its choosing, which is a cast written
another way, or with a function as in S. And it holds only what is
exported: the types of the symbols (and of the few variables they
mention) reachable from the module, after
`Typing_env.Pre_serializable.create` and `Serializable.create` have
cut the environment down; nothing with `-opaque`; types rebuilt from
approximations in classic mode. No variable of the term is there, so
it cannot serve the comparison with runs (request 3). As a source of
examples it is good, and R reaches it (above).

### P: a printer and a parser

`Flambda2_types.print` and `Typing_env.print` are public, so a test
could parse their output. It needs no access at all. But the printed
form is not a serialisation, and was not meant as one:

- it loses information: `print_head_of_kind_value` prints
  `Maybe_null { is_null = Some var }` as `?`, without the variable;
  fields at their default are left out (`print_field ~is_default`);
- it depends on flags (`Flambda_features.unicode ()`, colours);
- names are printed, not identified: the test would have to map the
  text of each variable, symbol, code id and slot back to the object.

So the printer would have to change (which changes the output of the
`-d` flags), and the parser would be new trusted code, about as long
as the converter, to be kept in step with a format that nobody
promised to keep. The hook of section 3 would still be needed.

## 3. The hook in Simplify (request 3), under option R

Two calls of the one public function.

`simplify/simplify_let_cont_expr.ml`, first line of the body of
`simplify_handler`:

```ocaml
  TE.notify_test_observer (DA.typing_env dacc) ~at_handler:cont;
```

Every handler that Simplify simplifies goes through this function: a
non-recursive handler, each handler of a recursive group, and each
specialised copy of a handler. The environment is the downwards one at
the entry of the handler: the environment at the fork, the join of the
uses, the parameters (with the parameters added for unboxing and for
lifted continuations) defined and given their types.

`simplify/simplify.ml`, in `run`, after `final_typing_env` is
computed:

```ocaml
  TE.notify_test_observer final_typing_env ~at_handler:return_continuation;
```

The final environment is the one at the single use of the return
continuation of the unit (or an environment with only the module
symbol, if the unit never returns). It is the environment before it is
cut down for the `.cmx` file, and before the reaper. Reporting it
under the return continuation of the unit means that no second
function and no marker are needed: the test knows that continuation
from the unit.

What the test is told to expect, since the simplest hook reports what
Simplify does and not what remains:

- handlers that are not in the output term: a handler inlined at its
  single use, the first pass over a handler that is then specialised,
  inlining that is tried and rejected. The test matches by
  continuation against the output and counts the rest;
- parameters of an output handler that the environment does not know
  (made on the way up); the test asks `mem` before `find`;
- its function must only read. `find` on a name of another unit calls
  the resolver, which may load a `.cmx` file.

Not done, and where it would go if a later version of the tests asks:
after each `Let` (one call in `simplify_let_expr.ml`, with the bound
pattern; it needs a second function, or a wider argument); at the
entry of each function body (`simplify_set_of_closures.ml`).

### 3.1 What the environments are keyed by

Simplify opens each binder of its input with `pattern_match`, which
gives fresh names; call them S. Its typing environments are keyed by
S, and it builds the output term with S (`Let_expr.create`,
`Continuation_handler.create`, ... are given the same names). So the
names *stored* in the output term are the names of the environments.

### 3.2 The gap: a test cannot see the stored names

Every opening of a binder that `terms/flambda.mli` exports freshens:
`Let_expr.pattern_match`, `Continuation_handler.pattern_match`,
`Non_recursive_let_cont_handler.pattern_match`,
`Recursive_let_cont_handlers.pattern_match` and
`Function_params_and_body.pattern_match` all end in
`Name_abstraction.pattern_match`, which calls
`Bindable.import_and_rename`, and that makes new variables and
continuations (`nominal/renaming.ml`, `bind_variable` and
`bind_continuation`; also when the renaming has an import map). So a
test that walks the output term sees names A, different from S, for
every bound variable, parameter and continuation, and no public
function relates A to S. Symbols, code ids and slots are not renamed,
so the check of symbols at the end of the unit is not affected, except
for the variables that the type of a symbol mentions.

This is what T7 and I had not seen when we agreed on "match by
identity against the output term". Three ways across:

**N1 (recommended): export the opening that the printer uses.**
`flambda.ml` prints terms with
`Name_abstraction.pattern_match_for_printing`, which does not freshen
unless `-dfreshen` is given; that is why the names in a dump of a term
are those in a dump of an environment. Export
it for the five constructs, next to each `pattern_match` and with the
same type:

```ocaml
  (** Like [pattern_match], but the bound names are not freshened
      (unless [-dfreshen] is given): they are the names that the term
      has, that is to say those it was built with, after any renaming
      that has since been applied to it. For printing, and for tests
      that must relate the names of a term to names recorded
      elsewhere. Not for code that transforms terms. *)
  val pattern_match_for_printing :
    t -> f:(Bound_pattern.t -> body:expr -> 'a) -> 'a
```

About three lines of code each in `flambda.ml` (the functor
`Name_abstraction.Make` already provides the function), five
declarations in `flambda.mli`, nothing at run time. The test builds its
model term with these, so the term it runs is written with S, and the
types convert under the same numbering of names. What a client can
newly do: read a term under the names it was built with. That is not
safe for code that copies or moves what it reads (names may be
captured), which is why the name says what it is for.

**N2: no change; the test matches names by their strings.**
`Variable.name` and `Continuation.name` survive renaming. The test
pairs a name of the output with a name of an environment when the
string is the same and is unique on both sides in the scope at hand,
and counts what it cannot pair. Complete for examples written by hand
with distinct names; partial otherwise: names made by Simplify repeat
(`unboxed_...`), code inlined twice repeats its names, and the
continuations the compiler makes are all called `k`. More trusted code
in the test, and a wrong pairing is possible.

**N3: a test-only switch that stops `Name_abstraction.pattern_match`
freshening.** The smallest change (one reference, one branch), and the
test's traversal stays as it is. But the branch is on the function
that Flambda 2 calls most, and a global switch that changes what
opening a binder means is a hazard out of proportion with the need.
Not proposed.

## 4. Behaviour and cost when no test is registered

`notify_test_observer` reads one reference and branches. Simplify
calls it once for each continuation handler it simplifies and once for
each unit; the arguments are two field reads from the downwards
accumulator and need no allocation. No flag, no change to any output.
The observer can only be set by code linked into the same process, so
the compiler as shipped never has one.

## 5. Files, and the other series of production changes

Accessors (done): `types/grammar/type_grammar.{ml,mli}`, the
`Block_size` submodule only.

Option R: `types/env/typing_env.{ml,mli}`, `types/flambda2_types.mli`,
`simplify/simplify_let_cont_expr.ml`, `simplify/simplify.ml`; a test
in `tests/api_tests/`.

N1 of section 3.2: `terms/flambda.{ml,mli}`, and its test in
`tests/api_tests/`. A commit of its own.

X3's flag touches `driver/oxcaml_{flags,args}`, `ui/flambda_features`,
`types/grammar/type_grammar.{ml,mli}` (a structural `equal`, far from
`Block_size`), `types/env/join_env.ml`, the two meet-and-join files,
and `tests/api_tests/` (its own files and `dune`). The two series
share `type_grammar.{ml,mli}` and `tests/api_tests/dune`, in different
places.

## 6. Questions for the human

1. Is option R acceptable as the "other way"? If not, S is the
   fallback: it is smaller in the types library, but puts the way to
   the representation in the public interface.
2. The names: `Typing_env.notify_test_observer` (public) and
   `Typing_env.For_testing.set_observer` (internal). And should the
   reference live in `typing_env.ml`, or in a module of its own?
3. The hook is not behind a flag: it is a load and a branch for each
   continuation handler. Is that acceptable, or should the two calls
   in Simplify be guarded by an existing flag?
4. For the comparison of types with runs only: may the terms export
   the opening that does not freshen (N1 of section 3.2), under the
   name `pattern_match_for_printing`? If not, the tests match names by
   their strings (N2) and say what they could not pair.

## 7. What building them showed

The observer and the openings were built and run before this note was
closed. Their tests are `tests/api_tests/typing_env_observer.ml` and
`tests/api_tests/binder_openings.ml`; the rest below is from an
experiment that does what those tests do, on every example.

**The openings give the names of the term, apply a renaming that is
still delayed, and freshen with `-dfreshen`.** The second test checks
the three: a handler built in the test is opened twice with the
parameter it was built with; after `apply_renaming` of `x` to `y` its
parameter and the argument in its body are `y`; a unit with the five
constructs binds the same variables and continuations each time it is
opened for printing, none of them when opened with `pattern_match`,
and none of them for printing once `-dfreshen` is set.

**The observer works under `Flambda2.flambda_to_flambda`**, which is
how the tests will call Simplify. The test receives the environment at
the start of the handler and at the end of the unit, reads the module
block through the grammar of types, and asks the library's own prover
(`Provers.prove_equals_tagged_immediates`, on the internal environment
and type) what the parameter of the handler is: one of `{ 10 20 }`.

**The parameter of a handler has the join of its arguments only with
`-flambda2-join-points`** (the default at `-O3` only;
`simplify/join_points.ml`). Otherwise a handler with several uses is
given unknown types for its parameters, and a comparison with runs
checks little. The tests must set it.

**On the 27 examples of `tests/semantics`** (26 are simplified; one is
there to be refused), at the default level and at `-O3`, with the same
counts:

- 29 handlers and 26 ends of unit were reported; no continuation was
  reported twice;
- the output terms have 14 continuation handlers, in 7 units. Opened
  with `pattern_match_for_printing`, all 14 are continuations that were
  reported. Opened with `pattern_match`, none is: this is the gap of
  section 3.2, measured;
- so 15 of the 29 reports are of handlers that are not in the output
  (inlined, or removed);
- of the 13 parameters of those 14 handlers, 11 are bound in the
  environment reported for their handler. The other two are parameters
  that Simplify made on the way up (below).

**A stored name can be bound in two places.** In `rec_cont.fl` the
output is, in short,

    let_cont finish (acc) = let r = acc in ... in
    let_cont rec loop (i, acc) = ... finish (acc) ... in
    loop (0, 0)

where the two `acc` are the same variable. `finish` was written with a
parameter `r`; its one use, inside the loop, passes the loop's `acc`.
Simplify gave `finish` a parameter for the variable that its argument
is, under that variable's own name, and bound `r` to it. So: the names
stored in a term are not unique (here in two handlers that do not
overlap; I have not seen a case that overlaps, and T7's converter
checks for one at each binder); and the environment reported for
`finish` knows `r`, which the machine binds only after the handler is
entered, and not the new `acc`. Both cases are ones the test already
skips and counts; a report after each `Let` would recover the first.
The same happens in `block_load.fl`.

**The `.cmx` files of the standard library are read through the same
function**, as section 2 says: a public environment whose resolver is
`Flambda_cmx.load_cmx_file_contents`, given to
`notify_test_observer` by the test, and `find` on the internal
environment for each symbol that `Serializable.ids_for_export` lists.
For `Stdlib__Option` that gave 18 types as `Type_grammar.t`, for
`Stdlib__List` 106; the type of the module symbol is the block of the
module's fields, as expected. The current unit must be set, and be
another unit than the one read.
