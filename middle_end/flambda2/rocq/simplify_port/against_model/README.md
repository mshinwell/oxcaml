# The port of Simplify against the model

This folder holds statements, proved by Rocq, that say of a PORTED function
of Simplify what a Spec file of THE MODEL says must hold. The model is the
rest of `middle_end/flambda2/rocq/`: its own types and semantics, and, in
its `*Spec.v` files, what Simplify may do. The port is the compiler's
Simplify itself, function by function (`../README.md`). A statement here
joins the two.

`FooSpec.v` has the statements, and the definitions that they need;
`FooProofs.v` has the proofs. A `Spec` file is to be reviewed. Of a
`Proofs` file only this is to be read: that each theorem has the statement
of its name. ONE FILE IS OF NEITHER KIND:
`Simplify_binary_primitive_named_locals.v` holds copies, with names, of
local functions of a ported file (the section "Where the ported Simplify
answers Invalid"). It is to be read against the port's file.

## What is here

| theorem | statement | says |
|---|---|---|
| `op_lhs_unknown_sound` | `op_lhs_unknown_statement` | SOUNDNESS OF THE COVERED ANSWERS of the ported `op_lhs_unknown` of `Int_ops_for_binary_arith`, at the tagged immediates, for the model's `eval_int_arith` |
| `op_rhs_unknown_sound` | `op_rhs_unknown_statement` | the same for `op_rhs_unknown` |
| `contracts_have_a_model` | `contracts_have_a_model_statement` | the four contracts below are together no contradiction |
| `tagged_op_lhs_unknown_sound` and thirteen more (the section "The seven kinds of integer") | `tagged_op_lhs_unknown_statement`, .. | the same soundness, for each of the SEVEN tables that the port has, at the width of any kind of integer of the model |
| `tagged_statements_agree` | `tagged_statements_agree_statement` | the statements of the first two theorems follow from those of two of the fourteen |
| `simplify_is_its_named_locals` and four more (the section "Where the ported Simplify answers Invalid") | `simplify_is_its_named_locals_statement`, .. | where the ported `simplify` of the tagged immediates answers Invalid for an operation whose right argument is known, the model's operation has no result |

The first three are in `FlambdaPortIntArithTableSpec.v` and
`FlambdaPortIntArithTableProofs.v`. The others are in
`FlambdaPortIntArithTableKindsSpec.v` and
`FlambdaPortIntArithTableKindsProofs.v`; the last five in
`FlambdaPortIntArithInvalidSpec.v` and
`FlambdaPortIntArithInvalidProofs.v`. This page is about the first
three until the section "The seven kinds of integer".

THE MODEL'S SIDE: `simplify/FlambdaSimplifyArithSpec.v`,
`int_arith_identities_statement`, which the model proves
(`int_arith_identities`). It says what the model's operation is at each
place of Simplify's table for integer arithmetic that answers `Exactly`,
`The_other_side` or `Invalid`. The model does not have the table.

THE PORT'S SIDE: `Simplify_binary_primitive.v`, the table itself
(`symmetric_op_one_side_unknown`, `op_lhs_unknown`, `op_rhs_unknown`), as
the compiler's `simplify_binary_primitive.ml` has it.

WHAT THE TWO THEOREMS SAY. For a machine width, an operation and a known
number that fits that machine width: the ported function never raises;
and if it returns an answer, the state is as it was and, for every number
`j` in the range of the model's tagged immediates as the other argument:
`Exactly r` means that the model's operation has the result that `r`
reads as; `The_other_side`, that it has the result `j`; `Invalid`, that it
has no result.

WHAT THEY DO NOT SAY.

- NOT COMPLETENESS, and not that two tables are equal. The answers
  `Cannot_simplify`, `Negation_of_the_other_side` and
  `Bitwise_not_of_the_other_side` have no obligation: a table that
  answered `Cannot_simplify` everywhere would have both theorems. A wrong
  answer among the three covered ones is found; a simplification that is
  missed is not.
- NOTHING OF A RUN THAT IS OUT OF FUEL. A function of which every run is
  out of fuel has both theorems. No termination is claimed. (A run that
  raises is not such a run: the theorems forbid it.)
- NOT THAT THE COMPILER'S NUMBERS HAVE 63 BITS. The model is of the 64-bit
  target only: its tagged immediates have 63 bits. For another machine
  width the theorems are true sentences about the model's 63-bit
  operation, and are not the model's word on the compiler's 31-bit
  immediates.
- NOTHING NEW ABOUT DIVISION BY ZERO: that `Div` and `Mod` by zero have no
  result is the model's own decision.
- NOTHING ABOUT THE OCAML THAT IS EXTRACTED. The theorems are about the
  Rocq text of the port (`../GUIDE.md`, section 8).

## What is assumed

The two theorems are CONDITIONAL. The numbers of the table are of the type
`Num.t` of `Number_adjuncts.For_tagged_immediates`, and the table calls
four functions of that module. `decl/Number_adjuncts.v` DECLARES all five:
each is a parameter, of which Rocq knows the type and no more. (The table
does not call the ported `Number_adjuncts.v`. Nothing here says that
`Num.t` is `Target_ocaml_int.t`.) So the statements have:

THREE THINGS THAT THE READER CHOOSES. The theorems hold for every choice
that has the four claims below.

| name | what it is |
|---|---|
| `machine_width` | the machine width that the table is given |
| `value : Num.t -> Z` | a reading of a number as an integer |
| `compatible : Num.t -> Prop` | the numbers that fit that machine width |

FOUR CLAIMS ABOUT THE COMPILER THAT ARE NOT PROVED. Each is a named
proposition of the Spec file, and a premise of both theorems. None is a
theorem.

| name | the declared entry (`decl/Number_adjuncts.v`) | what is assumed |
|---|---|---|
| `zero_is_0` | `Number_adjuncts.For_tagged_immediates.Num.zero` | at `machine_width` it never raises; if it returns, the number is compatible and reads as 0, and the state is as it was |
| `one_is_1` | `Number_adjuncts.For_tagged_immediates.Num.one` | the same, 1 |
| `minus_one_is_m1` | `Number_adjuncts.For_tagged_immediates.Num.minus_one` | the same, -1 |
| `equal_is_equality` | `Number_adjuncts.For_tagged_immediates.Num.equal` | ON TWO COMPATIBLE NUMBERS it never raises; if it returns, it says whether the two read as the same integer, and the state is as it was |

Each theorem also has, as a premise, that the known number is compatible.

WHY `compatible`. In the compiler these four are the functions of
`Target_ocaml_int` (`number_adjuncts.ml`, the module
`For_tagged_immediates`). A number there is of one of three widths; the
three constants are made of the width of the machine width that they are
given; and the test of equality ends in a fatal error on two numbers of
different widths (`target_ocaml_int.ml`). So a claim that `Num.equal`
never raises on EVERY pair would be false of the compiler. The claim is
made on the numbers that fit the machine width, and nothing says that
every number does.

NOTHING IS ASSUMED of the compiler's arithmetic on its numbers
(`Num.add`, `Num.mul`, ..): the table does not compute, it compares the
known number with three constants. No premise says that the known number
is in a range: a test that succeeds says that it reads as 0, 1 or -1.

THE CONTRACTS HAVE A MODEL (`contracts_have_a_model`): a type of numbers
with a reading, a set of compatible numbers and four functions that have
the four claims. A number of it has a mark that says whether it fits. Its
test of equality ends in a fatal error on two numbers with DIFFERENT
marks: one that fits and one that does not. On two numbers that both do
not fit it returns. The model shows that the claims are no contradiction,
and that the claim about the test does not ask it to return on every
pair. It does not show that a claim is true of the compiler.

## The seven kinds of integer

The table is in a functor of the port, `Int_ops_for_binary_arith`, over a
module of numbers. The port applies it at seven modules, as the compiler
does. The model's `int_arith_identities` is for every kind of integer of
the model. So `FlambdaPortIntArithTableKindsSpec.v` states, and
`FlambdaPortIntArithTableKindsProofs.v` proves, of EACH OF THE SEVEN
TABLES what the two theorems above say of the first, AT THE WIDTH OF ANY
KIND of the model:

| the port's module | its numbers (`decl/Number_adjuncts.v`) | the kind that the compiler pairs with it, and the model's width | the two theorems |
|---|---|---|---|
| `Int_ops_for_binary_arith_tagged_immediate` | `For_tagged_immediates` | `Standard_tagged_immediate`, 63 bits on the 64-bit target | `tagged_op_lhs_unknown_sound`, `tagged_op_rhs_unknown_sound` |
| `Int_ops_for_binary_arith_naked_immediate` | `For_naked_immediates` | `Standard_naked_immediate`, 63 bits on the 64-bit target | `naked_op_lhs_unknown_sound`, `naked_op_rhs_unknown_sound` |
| `Int_ops_for_binary_arith_int8` | `For_int8s` | `Standard_naked_int8`, 8 bits | `int8_op_lhs_unknown_sound`, `int8_op_rhs_unknown_sound` |
| `Int_ops_for_binary_arith_int16` | `For_int16s` | `Standard_naked_int16`, 16 bits | `int16_op_lhs_unknown_sound`, `int16_op_rhs_unknown_sound` |
| `Int_ops_for_binary_arith_int32` | `For_int32s` | `Standard_naked_int32`, 32 bits | `int32_op_lhs_unknown_sound`, `int32_op_rhs_unknown_sound` |
| `Int_ops_for_binary_arith_int64` | `For_int64s` | `Standard_naked_int64`, 64 bits | `int64_op_lhs_unknown_sound`, `int64_op_rhs_unknown_sound` |
| `Int_ops_for_binary_arith_nativeint` | `For_nativeints` | `Standard_naked_nativeint`, 64 bits on the 64-bit target | `nativeint_op_lhs_unknown_sound`, `nativeint_op_rhs_unknown_sound` |

ON THE 64-BIT TARGET: THE MODEL IS OF THAT TARGET ONLY. In the compiler
the width of the two kinds of immediates and of the native integers is
that of the target: it is less on a 32-bit target. The model has 63 and
64 bits for them, and no other width. At those three kinds a theorem
here is about the model's operation at the model's width; it is not the
model's word on a 32-bit target. The widths of the other four kinds are
the same on every target.

The statement of `K_op_lhs_unknown_sound` is `K_op_lhs_unknown_statement`,
and so for `rhs`. Each begins `forall kind : standard_int`, and then is
one of two general statements (`lhs_unknown_table_sound`,
`rhs_unknown_table_sound`: of any numbers, any table and any width) at
the module's numbers, its table and the width of `kind`.

EACH IS CONDITIONAL, in the way of the section before this one: the same
three things are the reader's to choose, and the same four claims are
premises, ON THE NUMBERS OF THE THEOREM'S OWN MODULE (`Num.zero`,
`Num.one`, `Num.minus_one` and `Num.equal` of the module of the second
column). So the fourteen theorems rest on TWENTY-EIGHT CLAIMS ABOUT THE
COMPILER THAT ARE NOT PROVED: four of one shape for each of the seven
declared modules. None is a theorem. What the section before this one
says of `compatible`, and of what is not assumed, holds of each.

WHICH KIND GOES WITH WHICH MODULE IS A READING. The model's identities
hold for every kind of the model. So each ported table is sound for the
model's operation at the width of EVERY kind, and each statement is for
every kind. The third column names the kind that the compiler pairs
with the module: in the compiler each module of numbers gives its kind
(`standard_int_kind`, in `number_adjuncts.ml`), and the kind of the
model is the one of the same name. The port cannot say it: `decl/`
declares each module's `standard_int_kind` as a parameter. So a theorem
here does not say that a table is used at its own kind. It says that its
covered answers are sound at whichever kind it is used.

WHAT THEY DO NOT SAY: what the two theorems above do not say, for each of
the seven. And nothing of the tables of the shifts, of the comparisons
and of the floats, which are other functors of the same ported file.

WHY TWO PAIRS OF FILES. The model's statements about terms
(`let_int_arith_tagged_statement`) are for the tagged immediates only,
and write the width as `tagged_width`. The first pair of files is the
statement that fits them, and it does not change.
`tagged_statements_agree` says that its two statements follow from the
two of the tagged immediates among the fourteen, at the kind
`Standard_tagged_immediate`. For the other six kinds the model has no
statement about terms. Of the model, each of the fourteen uses the
definitions of its operation and one theorem, `int_arith_identities`.

THE PROOF IS WRITTEN ONCE, in a functor over the argument of the port's
functor. Rocq takes the table of that functor at a module of `decl/` for
the port's own table at that module: each of the fourteen theorems is one
application.

WHAT `Print Assumptions` SHOWS of each of the fourteen today: eight
names, all parameters, of the same kinds as for the first two theorems.
Seven are declared entries of `decl/`: the type `Num.t` and the four
functions of the theorem's own module of numbers; that module's
`standard_int_kind`; the type `Target_system.Machine_width.t`. One is of
the kit: `ocaml_state`. Of `tagged_statements_agree` it shows the eight
of the tagged immediates: its statement names their table.

## Where the ported Simplify answers Invalid

`FlambdaPortIntArithInvalidSpec.v`, `FlambdaPortIntArithInvalidProofs.v`
and `Simplify_binary_primitive_named_locals.v`. They are about
`Binary_arith_like.simplify` of the ported `Simplify_binary_primitive.v`,
at the tagged immediates: the function that simplifies an integer
operation from the types of its two arguments.

| theorem | statement | says |
|---|---|---|
| `simplify_is_its_named_locals` | `simplify_is_its_named_locals_statement` | THE TIE: for all its nine arguments the port's `simplify` IS `simplify_with_named_locals`, the body of `simplify` with the four named copies of its local functions in it. No premise |
| `invalid_only_where_no_result` | `invalid_only_where_no_result_statement` | THE STEP: the copy of `only_one_side_known`, with the table `op_lhs_unknown`. If it returns an Invalid result, the model's operation has no result on any number in range and the reading of any known number |
| `simplify_invalid_is_sound` | `simplify_invalid_is_sound_statement` | the same of the port's `simplify` itself, for the runs that take the step |
| `fold_names_its_elements` | `fold_names_its_elements_statement` | the rule of the fold, given a list, says that the fold visits that list |
| `ported_create_is_not_invalid` | `ported_create_is_not_invalid_statement` | the port's text of `Simplify_primitive_result.create` does not make an Invalid result |

THE STEP. Where the prover of the right argument answers a set of known
numbers and the prover of the left does not know, `simplify` looks each
known number up in the table `op_lhs_unknown`, gathers a set of possible
results, and answers Invalid if the set is empty. The theorems say:
INVALID ONLY WHERE THE MODEL'S OPERATION HAS NO RESULT, for every known
number and every number in the range of the model's tagged immediates
as the left argument.

ON THE RIGHT ARGUMENT ONLY. With the left argument known the table is
`op_rhs_unknown`, and no line of it answers `Invalid`: there the same
statement would be true and would never apply. With the right argument
known, the table answers `Invalid` for `Div` and `Mod` on a known number
that reads as 0.

THE MODEL'S CHOICE THAT THIS RESTS ON. The model's operation has no
result in one place: `Div` and `Mod` on a zero divisor. The model marks
that as a choice for the human (the comment at `eval_int_arith` in
`semantics/FlambdaPrimitiveSpec.v`, decision D14; the Spec file quotes
it): it is right for a division that follows a test of the divisor, and
nothing checks it for the unsafe divisions. These theorems are the first
that are proved from the port to that choice. They agree with the model
because of it, and only under it.

THE NAMED COPIES. The four functions of the step (`result_unknown`,
`result_invalid`, `check_possible_results`, `only_one_side_known`) are
LOCAL to `simplify`, in the compiler and in the port: Rocq has no name
for them. `Simplify_binary_primitive_named_locals.v` has a copy of each,
with a name: the port's lines, with the variables of `simplify` that the
function uses as parameters. That file FOLLOWS THE PORT'S FILE, and so
the compiler's: it has the compiler's notice, and `../PROVENANCE.md` has
it as transcribed. A copy says nothing by itself. THE TIE makes the
copies the port's text: Rocq proves it by computing, and a copy that
differs from the port's lines, or a change of the port's lines, makes
that proof fail.

WHY THE COPIES ARE AT THE TAGGED IMMEDIATES, and not in a functor over
the argument of the port's functor. The port's functor
`Binary_arith_like` defines a type, the possible results, and Rocq makes
a new such type each time that the functor is applied. A copy inside a
functor of its own would apply the port's functor once more, and would
be about another type than the port's module has: the tie is then
refused. So the copies name the port's own two modules for the tagged
immediates; for another kind of integer the same lines are copied at
that kind's two modules.

AN INVALID RESULT IS DEFINED (`is_invalid_result`), not chosen by the
reader. `decl/` has the type of the results as an inductive type and a
record: a result is Invalid if it is `Simplified` of a record whose
`simplified_named` is `Or_invalid.Invalid`, which is the test of the
compiler's own `Simplify_primitive_result.is_invalid`.

THE PREMISES, of three kinds. The tie has none. The step has the first
two kinds; the statement of `simplify` has all three.

| kind | name | what it is |
|---|---|---|
| THE READER CHOOSES | `machine_width`, `value`, `compatible` | as for the table |
| THE READER CHOOSES | `nums`, `known` | a set of numbers and a list of numbers. They are not free of each other: the rule of the fold below is a premise, and it holds of a fold that returns only if the list is what the fold visits (`fold_names_its_elements`). A premise asks that every number of `known` is compatible |
| A CLAIM ABOUT THE COMPILER THAT IS NOT PROVED | `zero_is_0`, `one_is_1`, `minus_one_is_m1`, `equal_is_equality` | the four contracts of the table; they are used through the table's theorem |
| A CLAIM ABOUT THE COMPILER THAT IS NOT PROVED | `fold_visits .. nums known` | the declared fold of the sets of numbers, on `nums`, visits the numbers of `known`: each once, in some order, and no other. A rule in the form of a loop invariant, for every step and every invariant: if the invariant holds of nothing visited, and each step keeps it for a number of `known`, then the fold, if it returns, has it of ALL of `known`. It says nothing of this operation, of the state, of an exception or of a run out of fuel |
| A CLAIM ABOUT THE COMPILER THAT IS NOT PROVED | `create_is_not_invalid` | the declared `Simplify_primitive_result.create`, if it returns, does not return an Invalid result |
| WHAT SELECTS THE CASE (the statement of `simplify` only) | five premises under THE CASE | what five calls of `simplify` return on its arguments, if they return: `DA.denv`, `DE.typing_env`, the prover of the left argument (it does not know), the prover of the right (the set `nums`), `DE.machine_width`. Each is said for every state, because the statement does not know in which state the call is made: so it also says that the call answers nothing else from another state. They say nothing of what a prover's answer means |

WHY `create_is_not_invalid` STAYS A PREMISE, although the port has that
function's text. `simplify` calls `Simplify_primitive_result.create` of
`decl/`: a parameter, of which Rocq knows the type and no more. The
ported `Simplify_primitive_result.v` has the function's text, over a
record of its own, and `ported_create_is_not_invalid` proves the claim
of that text. That shows why the claim is believed. It cannot stand for
the premise: Rocq cannot give a parameter a definition, and nothing says
that the declared function is the ported one.

NOTHING IS ASSUMED of the other declared functions that the step calls
(the head of the Spec file lists them): the conclusion is about a run
that returns and about Invalid only, and holds whatever they return.

WHAT THEY DO NOT SAY.

- NOT THE MODEL'S PREMISE YET. The model's fourth conclusion asks
  `results (fun _ _ r => r = None)`, over the numbers that the MODEL's
  prover answers for the model's type of an argument. The conclusion
  here is over the list `known` and a reading `value` of the compiler's
  numbers: a precursor of it. STILL OPEN: that every number in range
  that the model's prover answers is the reading of a number of `known`
  (the crossing of the prover); and how the compiler's terms, types and
  environments are read as the model's.
- ONE DIRECTION, and not completeness: if the result is Invalid, the
  model's operation has no result. Not that Simplify answers Invalid
  wherever it has none.
- NOT THE OTHER PLACES where `simplify` answers Invalid: a prover that
  answers that the type has no number; both arguments known and no pair
  with a result.
- NOTHING OF A RUN THAT RAISES, OF THE STATE, OR OF A RUN OUT OF FUEL.
  The statements have the form `if_returns`: if the computation
  returns, the value has the property. The theorems of the table have a
  stronger form: no run raises, and the state is as it was. That form
  would need a claim about every declared function that the step calls;
  and the port's own text ends some runs of `simplify` in an exception
  (a fatal error, a failed assertion).
- Nothing of the answers with a term, of the type that the result
  variable gets, of the other six kinds of integer, or of the extracted
  OCaml.

WHAT `Print Assumptions` SHOWS of these five today. Of the tie and of
the theorem about `simplify`: 99 names. Of the step: 79. Of
`ported_create_is_not_invalid`: 39. Of `fold_names_its_elements`: one,
`ocaml_state`. ALL ARE PARAMETERS: declared entries of `decl/` (the
types and the functions that the body of `simplify`, and what it calls,
name: that is why the lists are long), two of the kit (`ocaml_state`,
`print_fatal_message`), and one that the ported file itself declares
(`K_Standard_int_or_float_to_kind`). The tie has its 99 because its
statement names `simplify`; its proof uses none of them.

## The bridge: three ways from the compiler's types to the model's

The port's functions are over the compiler's types as `decl/` has them.
The model's Spec files are over the model's own types. Each statement
says which of these it uses, for each thing that it crosses with.

1. DIRECT. The function touches only data that the port defines or that
   Rocq has, and what it calls is defined or has a proved law. No
   hypothesis is needed for the crossing.
2. A CONTRACT. For a thing that `decl/` only declares, the Spec file names
   a proposition that says what the declared function does, in the form
   of `../contracts/README.md`: for every fuel and state; on a stated
   domain; what holds of the value and of the state if the call returns;
   which exceptions it may raise. The claim is as weak as the proof can
   use. The statement has it as a premise. It is a claim about the
   compiler that is not proved, and it goes into the table above.
3. A MAP. Where `decl/` has the compiler's type as an inductive type or a
   record and the model has its own type for the same thing, the Spec
   file defines the map, constructor for constructor. The map reads a
   value; it gives no declared parameter a definition.

The theorems of the tables use a map for the operation
(`int_arith_op_of_port`, `signedness_of_port`) and four contracts for the
numbers. The theorems about Invalid use the first way for the result of
`simplify` (`decl/` has its type as an inductive type and a record, and
`is_invalid_result` is a definition on its constructors), and two
contracts more, for the declared fold and for the declared maker of a
result.

No file of this folder has an `Axiom`, a `Parameter` or an `Admitted`. A
contract is a hypothesis of a section in the Proofs file and a premise in
the statement. `Print Assumptions` of a theorem does not list its
premises. It lists the parameters that the proof reaches: those of
`decl/`, those of the port's kit, and whatever the model's theorems that
it uses rest on.

## How it is checked

    make against-model MODEL=ROOT        (in the port's folder)

`ROOT` is the root of a tree of this repository in which `make -C rocq
all` has run: the model's compiled files are read there. Nothing of the
model is compiled, and nothing is written in that tree. `ROOT` may be a
name from the port's folder: the tool makes one absolute name of it
first, reads the model by that name only, and prints it. The target makes
first what is missing or old of the port's real build (`make real`), then
compiles the files of this folder under `_build/against_model/`. For
each theorem Rocq checks that it proves the statement of the Spec file
that its line names. The target
prints of each theorem its statement's name, its WHOLE STATEMENT with the
definitions of the Spec files unfolded (the contracts stand in it as
premises), and what it rests on (`Print Assumptions`). Where it asks
Rocq, the target writes each name whole, from the library
(`SimplifyPortAgainstModel.FooSpec.STATEMENT`), and imports no file of
this folder. So Rocq prints each name of this folder with its file
before it (`FlambdaPortIntArithTableSpec.Num.t`). The same text is
kept in `_build/against_model/THEOREMS.txt`. The target also prints the
commit of the two trees that it reads, and whether either has a change
that is not committed. It does not know whether the model's compiled
files are of the model's `.v` files. `../tools/against_model.sh` says
how, which statuses of its commands decide what, and what it does not
judge.

THE TARGET IS NOT A PART OF `make`, of `make check` or of
`../tools/gate.sh`. The port's gate does not need the model. A commit
that changes this folder is checked by this target against a built model.

WHAT `Print Assumptions` SHOWS of the two theorems today: eight names,
all parameters. Seven are declared entries of `decl/`: the type `Num.t`
and the four functions of the table above; `standard_int_kind` of
`Number_adjuncts.For_tagged_immediates`, which one place of the table
names in an answer; the type `Target_system.Machine_width.t`. One is of
the kit: `ocaml_state`. The model's `int_arith_identities` is closed under
the global context.

## For the writer of the next file

- THE NAMES. `FooSpec.v` and `FooProofs.v`, both in this folder. The
  library is `SimplifyPortAgainstModel`: `From SimplifyPortAgainstModel
  Require Import FooSpec.` The port's real build is `SimplifyPort`, as
  everywhere. The model's libraries have the names of the model's
  `_CoqProject`.
- A THEOREM of a Proofs file is one line, `Theorem NAME : STATEMENT.`,
  where `STATEMENT` is a definition of the Spec file. The target reads
  that line, and Rocq checks that the theorem
  `SimplifyPortAgainstModel.FooProofs.NAME` proves the statement
  `SimplifyPortAgainstModel.FooSpec.STATEMENT`. The names are whole, and
  the target imports no file of this folder where it asks: a Proofs file
  that defines the statement's name again, or that has a module of the
  name `FooSpec`, does not change what is checked and printed. A helper
  is a `Lemma`; so is a result inside a module or a functor of a Proofs
  file.
- A SPEC FILE HAS NO MODULE OF ITS OWN (`Module X.` .. `End X.`): the
  target stops at one. It unfolds the definitions of propositions of the
  Spec files by their whole names
  (`SimplifyPortAgainstModel.FooSpec.NAME`). A short name for a module
  (`Module X := Y.`) is none.
- THE HEAD of a Spec file names the model's file and statement that it
  is about, the bridge that it uses, and what the statement does not say.
- A LOCAL FUNCTION OF A PORTED FILE has no name, and a statement cannot
  be about it. Do not change the ported file. Copy the local function's
  lines into a file of named copies (as
  `Simplify_binary_primitive_named_locals.v`: the notice of the ported
  file, a first comment that says which lines each copy is of, a row of
  kind transcribed in `../PROVENANCE.md`), with the variables that it
  uses as parameters; and PROVE THE TIE: that the ported function is its
  body with the copies in it, by `reflexivity`. Name the port's own
  modules in the copies: inside a functor of your own the tie is refused
  where the port's functor defines a type. A copy without a proved tie is
  worth nothing.
- TWO NOTATIONS `let* x := m in k`. The port's kit has one and the model's
  `OxCamlOption` has another, at another level. Rocq refuses to import
  both in one file. Import the kit; of the model, import what does not
  export that notation, and only require the rest.
- `Add` is the list's with the kit imported: write a constructor of the
  model with its module (`Model.Add`), and one of the port with its own
  (`P.Add`).
- DO NOT GIVE A SHORT NAME TO A WHOLE PORTED FILE (`Module X :=
  SimplifyPort.Simplify_binary_primitive.`): Rocq then copies the file's
  functors (17 seconds and 4.7 megabytes in the compiled file, when it was
  tried). A short name for one module of it is cheap.
- `decl/` has a file with the name of each ported file. Write a name of a
  ported file from `SimplifyPort`.
- The target refuses a line that begins `Axiom`, `Parameter`,
  `Conjecture` or `Admitted`, and the word `admit`, also in a comment.
  That is a rule of lines and words. It does not show that a file takes
  nothing without a proof: the reader of the file does, with the list
  that `Print Assumptions` prints.
