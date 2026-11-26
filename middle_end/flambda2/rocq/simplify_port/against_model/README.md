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
of its name.

## What is here

| theorem | statement | says |
|---|---|---|
| `op_lhs_unknown_sound` | `op_lhs_unknown_statement` | SOUNDNESS OF THE COVERED ANSWERS of the ported `op_lhs_unknown` of `Int_ops_for_binary_arith`, at the tagged immediates, for the model's `eval_int_arith` |
| `op_rhs_unknown_sound` | `op_rhs_unknown_statement` | the same for `op_rhs_unknown` |
| `contracts_have_a_model` | `contracts_have_a_model_statement` | the four contracts below are together no contradiction |

All three are in `FlambdaPortIntArithTableSpec.v` and
`FlambdaPortIntArithTableProofs.v`.

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
- NOTHING OF A RUN THAT IS OUT OF FUEL. A function that never returns has
  both theorems. No termination is claimed.
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
the four claims, among them a test of equality that ends in a fatal error
on two numbers that do not both fit. It shows that the claims are no
contradiction, and that the claim about the test does not ask it to
return on every pair. It does not show that a claim is true of the
compiler.

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

The two theorems here use a map for the operation
(`int_arith_op_of_port`, `signedness_of_port`) and four contracts for the
numbers.

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
model is compiled, and nothing is written in that tree. The target makes
first what is missing or old of the port's real build (`make real`), then
compiles the files of this folder under `_build/against_model/`, and
prints of each theorem its statement's name, its WHOLE STATEMENT with the
definitions of the Spec files unfolded (the contracts stand in it as
premises), and what it rests on (`Print Assumptions`). The same text is
kept in `_build/against_model/THEOREMS.txt`. The target also prints the
commit of the two trees that it reads, and whether either has a change
that is not committed. `../tools/against_model.sh` says how, and what it
does not judge.

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
  that line. A helper is a `Lemma`.
- THE HEAD of a Spec file names the model's file and statement that it
  is about, the bridge that it uses, and what the statement does not say.
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
