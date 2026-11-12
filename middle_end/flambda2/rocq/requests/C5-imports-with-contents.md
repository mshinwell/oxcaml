# C5: a unit run after the units it depends on

From C5, for V2 (the tool, the corpus and the tables), C2 (the
conversion), C3 (closures), V3 and the owners of the liftings (their
statements from the imports), C0 (well-formedness and the interface
of a unit), X5 (the validation of the compiler's own run), R1 (who
reviews it) and the human (the decisions, at the end).

It is a request with no prototype: nothing in a `.v` file or in the
tool changes with it. What is measured is measured with the tool as
it is, on units written for the purpose (section 4), and on C2's
counts over real units, which are not in this tree.

Paths of the model are in `middle_end/flambda2/rocq/`, and those of
the compiler in `middle_end/flambda2/`, unless they say otherwise.

## 1. What stops

`requests/C5-imported-symbols.md` made a symbol of another unit an
object whose contents the model does not know. That is enough for a
predefined exception, which is compared and raised and never read.
It is not enough for a module. A unit that uses another unit loads a
field of its module block and calls it:

    let length_plus_one l = List.length l + 1

is, before Simplify, a load of a field of the symbol of the other
unit and a call of what is loaded. In the model the load has no
value, so a run that reaches it is undefined. Three shapes, each a
few lines of OCaml, cover what real units do:

- a function that calls a function of another unit (above). Its
  unit is defined, as the load is in code that the unit does not
  run, and the validator compares the two bodies;
- a toplevel that calls one: `let three = List.length [1; 2; 3]`.
  The unit is undefined;
- a toplevel that reads one and keeps it, as `include List` does.
  The unit is undefined.

There is a second obstacle, which is not in the model. Simplify
reads the `.cmx` of the other unit: it puts the closure symbol in
the place of the load, makes the call direct, and inlines it if the
`.cmx` has the body. The tool runs Simplify itself, on the term
before read back from its text, with no load path: its Simplify
finds no `.cmx` and leaves the load and the call as they are. So for
a unit that uses another unit the term after that the tool
validates is not the one the compiler makes.

C2 counted, over 119 real units (the modules of the standard library
and a directory of the compiler's tests) and their 4,580 functions:

| | Units | Functions |
|---|---|---|
| a symbol of another unit is read or called | 102 | 984 |
| ... and nothing else that the model lacks | 20 | 644 |
| a predefined exception is named | 59 | 169 |

Of the 644 functions that need only this: 138 pass a field of the
other unit on, store it or compare it; 536 call one. With the `.cmx`
at hand, the compiler's Simplify resolves at least one load from the
other unit's module block in 541 of them; it inlines at least one
call in 323, and leaves no call of the other unit in 292; it leaves
a call of the other unit's code in 177. 62 units load a field of
another unit at toplevel, and for 20 of the units that the tool reads
today that load is where the run becomes undefined.

## 2. What the compiler has

- Before Simplify a function reaches another unit only by loading a
  field of its module block. After it, the term names the other
  unit's closure symbols, as values and as callees, and its code
  ids, in direct calls. X5 is counting what else it names (the sets
  of closures of inlined code, the other unit's lifted constants).
- A `.cmx` holds, for its unit (`cmx/flambda_cmx_format.ml`): the
  types of the symbols that can be reached from the module symbol,
  and the code, with a body only for code that may be inlined and
  with the metadata alone for the rest (`cmx/exported_code.ml`,
  `add_code`: code whose inlining decision is that it cannot be
  inlined is remembered by its metadata only). It is not the term of
  the other unit.
- The compiler has its own reduction of the type of such a symbol to
  what a static binding can say (`types/env/typing_env.ml`,
  `extract_symbol_approx`, reached by
  `Flambda_cmx.load_symbol_approx`; it is what classic mode uses): a
  constant; another symbol; a closure, with its code id, its
  function slot and the code or its metadata; an immutable block,
  with its tag and, for each field, the same again; or unknown.
  Of a closure it gives no more than that: not the other functions
  of its set, and not its value slots. Simplify itself works from
  the types, which say more: the whole set of a closure and what
  its value slots hold, the contents of a boxed number, a block
  that is one of several.
- Loading (X5 read this; `cmx/flambda_cmx.ml`). A `.cmx` is read the
  first time a symbol or a code id of its unit is asked for, and
  then all its code is merged. A unit that is never asked about is
  not read. A failure is remembered for the whole run: with a
  missing `.cmx`, or a unit compiled with `-opaque`, Simplify goes
  on with nothing known of that unit. A member of a pack is read
  from the pack's `.cmx`. The variables and continuations of
  imported code are renamed at each import; symbols, code ids and
  slots keep their names. A unit's own `.cmx` records each unit
  that was asked for, with the digest of the file read, or with
  none where the unit is opaque or its file was not found.
- In the process that ran Simplify the loaded contents can be had
  again (`Compilenv.get_unit_export_info`, and a loader made by
  `Flambda_cmx.create_loader`). Asking is not free of effect: for a
  unit that Simplify did not ask about, the file is read then, and
  the unit is added to those that the compilation records in the
  `.cmx` it writes (`get_unit` in `middle_end/compilenv.ml`, from
  the root of the repository). Nothing
  says whether a unit is already loaded. The tool writes no `.cmx`,
  and today is given no directory to read one from; the validation
  of the compiler's own run is in the compiler's process.
- The text of terms cannot say any of this: the parser refuses the
  declaration of a symbol of another unit, there is no syntax for
  code that has metadata and no body, and the printer writes a code
  id of another unit without its unit.

## 3. The design

**A unit is validated given what the `.cmx` say.** The conversion
puts, in front of both terms of a check, one prefix of static
bindings: what the `.cmx` of the other units say of the symbols and
the code that the two terms name. The two terms validated are the
prefix followed by the unit before, and the same prefix followed by
the unit after. The static bindings of the model can say what the
reduction of section 2 says:

- a block, by `Bind_symbol` of a block whose fields are constants
  and symbols;
- a closure, by `Bind_symbol` of the closure at its function slot of
  a set that has this one function and no value slot
  (`Static_const_closure_of_set`, at the closure's own slot: a
  projection has no value on a closure at another slot than the one
  it names). That is less than the other unit has, and it shows: a
  body that reads a value slot of its own closure, or goes to
  another function of its set as mutually recursive functions may,
  has no value there, and a run that reaches it is undefined. The
  verdict is then empty, not wrong. C3 has confirmed it: the model
  has no value exactly where what is missing would be read
  (`project_value_slot` of a slot the closure has not got,
  `project_function_slot` to a slot its set has not got), no
  primitive counts slots or functions, and `Phys_equal` has no value
  on two closures. The prefix is converted with the presentation of
  sets that the two terms have, and is written for named function
  slots first. The types have the whole set; reading them is the
  second step (section 7);
- code that has a body, by `Bind_code` of the body converted as the
  code of the unit is;
- code that has no body: nothing. Its code id stays bound to
  nothing, and a call of it is undefined, as a call of an import is
  today. The call is still compared: the two terms have the same
  direct call.

What the prefix names and does not bind is an import as today: a
symbol of which nothing is said is `Static_imported`, of the class
`Import_data`, or `Import_identity` for a predefined exception. So
the prefix replaces no part of the first request; it puts contents
in front of it.

The prefix is made on demand: of the names that the two terms
mention, and of the names that the bodies and the blocks so bound
mention in turn. A field of a block that is a symbol and is asked
for by nothing stays an import. Binding less is always right: what
is not bound is not looked into. It is converted once, and is the
same term in front of both: the compiler renames the variables and
continuations of imported code at each import, so two conversions
would agree up to bound names only.

**What is assumed, and where it is said.** One new entry of the
trust ledger: that when the unit starts, what the prefix says of
each symbol it binds is true of the object, and each code id that it
binds has that code. Of a block the prefix says its tag and its
fields. Of a closure it says its code and its function slot and
binds it with nothing else; the model has no value where anything
else of it is read. That is: the `.cmx` are right about their
units, and they are the `.cmx` of the units that the program is
linked with. It is stated for each unit read, by the digest of its
`.cmx`. The tool names the units read; it prints the digests only
when asked, as it prints the terms, since the `.cmx` of a test is
made by the build and its digest moves with the compiler. The units
read are those that the run of Simplify read. The tool can ask the
loader for any unit, as it writes no `.cmx`. In the compiler's own
process asking changes what is recorded, so there the prefix is
made of the units already recorded, or a way to ask without loading
is added to the compiler, which is not ours to add. Nothing is
assumed of what the prefix
does not bind. Simplify is not trusted for it: the conversion reads
the `.cmx` through the compiler's loader and its reduction, and not
through anything that Simplify concluded.

**The statements.** With a prefix, the validator's theorems apply to
the two prefixed terms as they are, and no statement changes:

- where the prefix leaves no import, the theorem from the empty
  static environment (`FlambdaValidateSpec.validate_unit_sound`),
  for every verdict;
- where it leaves imports, the theorem from the imports
  (`FlambdaValidateImportsSpec.v`), for the three verdicts it has
  today and for no other. A prefix changes nothing there: a verdict
  that lifts, and one that rests on a removal of static bindings
  from the term after, are outside that theorem with a prefix as
  without. A unit that defines a function is validated once its
  closures are lifted: for those the liftings are to be stated from
  the imports, which their owners already owe.

One small statement is mine to add, so that the ledger can say the
thing in its own terms: two terms that follow one prefix refine each
other from an environment exactly when the terms without the prefix
do from the environment that the prefix makes of it. The verdict is
then "the unit after refines the unit before, each run from the
static environment that the `.cmx` describe", and the prefix is how
it is checked.

**A field of which the `.cmx` say nothing** is the one thing that the
model cannot say today. A module block has such fields wherever the
module computes a value as it is initialised (a table, a channel).
The field is not a symbol: it may be an immediate, or an object that
is mutable. `Import_data` is wrong for it, as the model answers
false to `Phys_equal` of an import against an immediate. Proposed: a
third class, `Import_unknown`, of which no primitive has a value,
`Phys_equal` included; it can be passed, stored and returned. The
prefix then gives such a field a symbol of its own, of that class.
Without it, a block with one unknown field cannot be bound at all,
and every load from that module stays undefined. The first units
(section 6) do not need it; the standard library does.

**From which environment.** The three verdicts that hold from the
imports hold from more: the proof uses nothing of the static
environment of the imports but that the names removed from the term
before do not occur in it, and nothing of the heap. So my two
statements can be made from any static environment in which those
names do not occur and from any heap, with the imports as the
instance that the tool runs. That is the form in which a call of
code that has no body means something: it holds whatever code the
environment binds there. I propose to restate my two that way. I do
not propose it for the liftings: from the imports their invariants
are about objects that hold nothing, and that is the cheaper thing
to ask of their owners first.

**The four cases.**

- (a) A symbol of another unit that is passed, stored or compared:
  the first request. Nothing new.
- (b) A function of another unit that is called, where the call
  stays. The load is resolved by the prefix and the call is direct
  in both terms. If the `.cmx` has the body, a run that makes the
  call has its meaning. If not, the run is undefined from there in
  the model, and the pair is compared all the same. A meaning for
  that call is the same question as a meaning for a C call (a call
  whose code is not in the model, which may read and write the
  heap), and should be answered once, with it; under my two
  statements as restated it already means "whatever code is there".
- (c) A function of another unit that is inlined, or a field that is
  read from the `.cmx`: the main case, and what the prefix is for.
- (d) A field of another unit read at toplevel: the load has a value
  as soon as the prefix binds the block. With the third class this
  holds of a block that has unknown fields too.

**What the tool prints.** A verdict that rests on a prefix says so,
and is counted apart (V2: a table of its own, never added to the
plain count). The wording follows what is frozen for a unit with
imports, and is the orchestrator's to settle. Proposed: "validated
with its imports, given the .cmx of N of them: ..." where the
theorem applies to the two runs shown; "validated with nothing else
imported, given the .cmx of N: ..." followed by "not validated with
its imports: ..." where it does not. Before the verdict, the units
whose `.cmx` were read.

## 4. What was measured

With the tool as it is, on seven units written by hand, which are
not in this tree, in which the static bindings that stand for another
unit (a function, its closure symbol, a module block) come first, as
a prefix would:

| The unit | Verdict |
|---|---|
| a function that calls the other unit's function; Simplify inlines the call | validated, once closures are lifted |
| the same, the other function never inlined; the call stays, direct | validated, once closures are lifted |
| a toplevel that reads two fields of the other unit and keeps them | validated, once normalised and unused static bindings removed |
| a toplevel that calls the other unit's function; inlined | the same |
| the same, never inlined | the same |
| a toplevel that reads a field which is an import (as an unknown field would be) | the same; it is one of the three verdicts that hold from the imports |
| the same in a unit that also defines a function | validated once closures are lifted: with nothing imported only |

So the validator needs nothing new to follow Simplify through a
prefix: it already reads what a symbol in sight is bound to, makes
the call direct and inlines it. And the last line is the limit that
matters: a unit that defines a function and keeps one import is
validated today with nothing imported only, until the liftings are
stated from the imports.

This is a measure of the validator, not of the proposal: in these
units the tool's Simplify sees the prefix as part of the unit, and
may change it; with the proposal the prefix is the same in both
terms. Code with no body could not be tried: the text of terms
cannot say it.

Not measured: how many of the 102 real units would be validated.
That needs the conversion of section 3, and those units need the
heap and C calls as well; 20 need only this.

## 5. What it leaves undefined, and what it does not cover

- A run that calls code of another unit which has no body in the
  `.cmx`, or whose body the model cannot express (the conversion
  leaves such code unbound; it does not refuse the unit).
- A run that reads a field of which the `.cmx` say nothing, or that
  compares one.
- A recursive module: its initialisation calls functions of the run
  time's own module for them, which fill in blocks that the unit
  then reads. That is a call with no body that writes to the unit's
  blocks: the abstract call of (b), with the heap.
- What Simplify knows from the types and the reduction does not say
  (the set and the value slots of a closure of another unit, a
  boxed number). Where Simplify uses it the unit is not validated,
  and where a body in the prefix needs it the run is undefined.
  That is a loss of completeness and never of soundness: the prefix
  says less than the `.cmx`, not more. The rewrites that read the
  value slots known of every set of a term read those of the
  prefixed term: a closure of the prefix has no slot and gives no
  slot a value, and a run through it is undefined in the term
  before, so the verdict is empty for that run too.
- The other direction. The theorem is of the run of a unit, which
  is its initialisation. Of the code of a function that this run
  does not call it says nothing, with or without imports: the
  validator compares that code, and no statement is about a later
  call of it from another unit. A statement about a program of
  several units is not in this request.
- The round trip of the conversion checks a unit without its prefix,
  as the text cannot declare what the prefix binds. The conversion
  of a `.cmx` is covered by no such check.

## 6. The work, by owner, and what comes first

In this order. The first three give the first units; none of them is
a proof.

1. V2: the tool takes a load path, as an option that the rules of
   today do not pass, so that the units of the corpus print what
   they print. A directory of pairs of units beside the corpus, with
   its own rules: the first unit compiled, the second compiled
   against it and checked with the load path. No standard library.
   The first pairs: the three shapes of section 1, and one where the
   function of the first unit is never inlined, so that its code has
   no body. Small. V2 has accepted it as written, after its series
   in hand; each unit of a pair is checked as any unit of the corpus
   is.
2. C2 with V2 (the conversion is in the tool): the prefix. From the
   loader, for each name of another unit that the two terms mention:
   the reduction, converted to static bindings; the bodies, by the
   conversion of code that exists; once for both terms, in the one
   numbering; the names so bound taken out of the list of imports.
   Medium: about the size of the conversion of static constants. It
   is trusted OCaml; the ledger entry is mine to write, with them.
   A commit of its own, apart from the option, with V2's word on it
   as on any change to the tool.
3. Me: the statement that relates a prefix to the environment it
   makes; the wording of the ledger; my two statements restated
   from any static environment, if that is agreed. Small.
4. V3, C3 and the owners of the liftings: their statements from the
   imports, already owed. This decides how many real units are
   validated with their imports, and it is the large item. V3 has
   read its proofs for it: all are simulations set up at the first
   state, and all but one go through from the imports, given that
   the result of a pass binds no import and a short fact about the
   imports for the invariant of each. The one is the moving of
   static bindings to the head of the unit, whose check of scope
   must be told that the imports are in scope from the start: a
   definition changes there. V3's estimate is a day for the first
   and a day for the second, after its series in hand and after
   C4's move of the same proofs to the heap.
5. Me: the third class. Small in my files; one more case wherever a
   class is matched, as the second class was.
6. C0: the list of imports in the interface of a unit, and the row
   of well-formedness for symbols and code ids, which must admit a
   code id of another unit that is bound to nothing. As already
   proposed.
7. C3 has confirmed the closure of another unit bound at its
   function slot, in a set of one, with no value slot: it is whole
   and bound for the checks of sets, and it goes through the choice
   of presentation with the two terms. C3 will state its reading of
   known value slots from any static environment that stores no code
   and whose values have their slots as the unit says, of which the
   imports are an instance; no premise on what the unit binds is
   needed there.
8. X5: the same prefix in the validation of the compiler's own run,
   where the loaded `.cmx` are at hand; and the counts of what the
   terms after of real units name of other units.
9. Later, and with C calls: a meaning for a call of code that has no
   body.

## 7. Options not taken

- **The type of each symbol given to the validator**, and a
  normalisation that reads types. It says everything Simplify knows.
  It needs the meaning of a typing environment as a property of
  static environments, a validator that takes one, and the
  conversion of types trusted for it. The prefix needs none of
  these, and the reduction it rests on is the compiler's own.
- **The prefix made from the types, not from the reduction**, so
  that a closure has its whole set and its value slots. It is the
  second step, when the first pairs show what the reduction loses:
  the prefix is the same, and the conversion reads more, with the
  conversion of types that the tests of types already trust.
- **The term of the other unit in front**, so that nothing is
  assumed of the `.cmx`. Its initialisation would run in the model
  before the unit, with all that it needs (the heap, C calls), and
  the compiler does not have that term when it compiles the unit.
- **The prefix made from the files by a separate reading**, rather
  than from what was loaded in the run. It may know more than
  Simplify did, which is harmless for the theorem, but it is another
  assumption than the one the run made. The tool is in the process
  that ran Simplify and can take what was loaded.
- **A body of `Invalid` for code that has none.** It makes a call of
  that code undefined, as leaving the code id unbound does, by a
  convention of the conversion in place of a rule of the machine.
- **An unknown field as a variable** that the unit does not bind,
  with the theorem over all its values. It says exactly what is
  meant. The unit is then not closed, and the folding of what
  symbols are bound to asks for constants with no variable in them.

## 8. Decisions for the human

1. **Is "validated given what the `.cmx` say" an acceptable
   verdict**, counted apart, with the assumption in the trust ledger
   for each `.cmx` by digest? Recommended: yes. It is what the
   compiler itself assumes when it reads a `.cmx`.
2. **The prefix from what the run loaded, or from the files.**
   Recommended: from what was loaded, as X5 advises. In the
   compiler's own process that means the units the compilation has
   recorded, unless the compiler gains a way to ask whether a unit
   is loaded.
3. **A third class for a value of which nothing is known.**
   Recommended: yes, when the first pairs are in and before the
   standard library.
4. **My two statements from any static environment and any heap**,
   with the imports as an instance. Recommended: yes; it is what
   gives a call of code with no body a meaning in the three verdicts
   that do not lift.
5. **The order**: pairs of units and the prefix first, the liftings
   from the imports next. Recommended as written in section 6.
6. **The wording of the tool's lines** for a verdict that rests on a
   prefix (section 3).
