# The port of Simplify: contracts

A CONTRACT is a statement that a proof assumes of a PARAMETER of the real
build: a function or an exception that `decl/` declares, a parameter that a
ported file declares itself, or a parameter of the kit
(`monad/real/Port_monad.v`). A parameter says its type and no more.
`Parameter f : a -> M b.` does not say that `f` returns, what it returns, or
that it raises nothing. `Parameter E : exception unit.` does not say the
name of `E`. What a proof needs beyond the type is written in this folder,
under a name, and the theorem that needs it has it as a premise.

A contract is NOT an axiom. No file of this folder has an `Axiom` or a
`Parameter`: Rocq assumes nothing here. A contract is a definition of a
proposition; a theorem with a contract as a premise is proved whether the
contract is true or not. THAT A CONTRACT IS TRUE OF OCAML'S FUNCTION IS
PROVED NOWHERE. Whoever reads a theorem as a statement about OCaml's run
answers for each of its premises (`GUIDE.md`, section 8).

The files of this folder are compiled by `make real` only. Nothing of them
is extracted, and no ported file requires one.

## The form

    (* Of any function of the type of [M.f]: what it does. *)
    Definition does_this (f : a -> M b) : Prop := ...

    (* THE CONTRACT. *)
    Definition f_does_this : Prop := does_this M.f.

    (* A model. *)
    Example f_does_this_has_a_model : does_this (fun x => ...).

1. A contract is a `Definition` of type `Prop`: a predicate on ANY value of
   the parameter's type, applied to the parameter. (The contract of the
   name of an exception is `named E "NAME"`, of `Kit_laws.v`: the predicate
   is `fun e => named e "NAME"`.)
2. Beside it stands a MODEL: an `Example` that proves the predicate of a
   value that Rocq defines. It shows that the contract is no contradiction.
   A model does not show that the contract is true of OCaml.
3. Contracts of ONE parameter have ONE model that has them all (one
   `Example` proves them all of one value): two contracts that each have a
   model can contradict each other. Contracts of different parameters need
   no common model as long as each speaks of its own parameter only.
4. A contract of a function is stated for EVERY fuel and every state, in
   the forms of `Kit_laws.v`: `wp`, `spec`, `returns_or_fatal`. So it says
   nothing of a run that is out of fuel.
5. A contract says nothing that the real monad has no word for: nothing of
   a backtrace, of what is printed, of time or of memory.
6. A theorem takes its contracts as premises: a `Hypothesis` of a section,
   or `contract -> ..`. Never an `Axiom`. `Print Assumptions` of the
   theorem then lists parameters of the port and of the kit and nothing of
   this folder; the contracts are in the theorem's statement, where its
   reader sees them.
7. The weakest contract: of a call, that it returns or ends in a fatal
   error (`returns_or_fatal`, in `Kit_laws.v`). It is what a proof needs of
   each call so that a fatal error stays the only exception.

A PREMISE ABOUT ONE CALL of one ported function (this printing, with these
printers) may stand in the file of the proof instead, as a `Hypothesis` of
the same form. It is an assumption like a contract. The head of that file
says how many it has and what they are about.

## The names of the files

| file | contracts of |
|---|---|
| `contracts/Port_monad.v` | the parameters of the kit |
| `contracts/NAME.v` | the parameters of `decl/NAME.v` |
| `contracts/ported/DIR/Foo.v` | the parameters that the ported file `DIR/Foo.v` declares itself |

The Rocq name of `contracts/NAME.v` is `SimplifyPort.contracts.NAME`. A
file that requires it says `From SimplifyPort.contracts Require NAME.` and
then gives it a name of its own (`Module Contract :=
SimplifyPort.contracts.NAME.`), since `NAME` alone is also the declared
module, and often a ported file.

## The name of an exception

The real monad knows ONE thing of an exception: its name. Two exceptions of
one name that carry one type are one exception; two of different names are
two (`Kit_laws.v`, section 1). An exception of the kit has its name by its
definition. A declared exception is a parameter, and its name is a
contract. THE RULE OF NAMES says which name:

- the name of the compiler's file that DEFINES the exception, without its
  folder and with a capital first letter; then each module of that file
  inside which the definition stands; then the exception; with dots
  between. `Simplify_simple.Simple_not_in_scope`,
  `Rebuilt_expr.Matching_for_unique_handler.Match_failure`;
- for an exception of the standard library, the same with the library's
  file: `Queue.Empty`;
- for an exception that OCaml defines before any file, its name alone:
  `Not_found`, `Invalid_argument`. (The kit's own: `Misc.Fatal_error`,
  `Not_found`, `Assert_failure`, `Division_by_zero`.)

TWO DECLARATIONS OF ONE EXCEPTION OF OCAML get the one name. There is one
such pair today: `Unboxing_epa.Invalid_apply_cont` is declared in
`decl/Unboxing_epa.v`, which `unboxing/Unbox_continuation_params.v` handles,
and in the ported file `unboxing/Unboxing_epa.v`, which raises it. With the
two contracts the two parameters are one exception
(`proofs/unboxing/Unboxing_epa_exceptions.v`).

The names that the rule gives the eight declared exceptions:

| declaration | name | contract |
|---|---|---|
| `Simple_not_in_scope` of `Simplify_simple.v` | `Simplify_simple.Simple_not_in_scope` | `contracts/ported/Simplify_simple.v` |
| `Invalid_apply_cont` of `unboxing/Unboxing_epa.v` | `Unboxing_epa.Invalid_apply_cont` | `contracts/ported/unboxing/Unboxing_epa.v` |
| `Invalid_apply_cont` of `decl/Unboxing_epa.v` | `Unboxing_epa.Invalid_apply_cont` | `contracts/Unboxing_epa.v` |
| `Prevent_current_unboxing` of `unboxing/Unboxing_epa.v` | `Unboxing_epa.Prevent_current_unboxing` | `contracts/ported/unboxing/Unboxing_epa.v` |
| `Matching_for_unique_handler.Match_failure` of `Rebuilt_expr.v` | `Rebuilt_expr.Matching_for_unique_handler.Match_failure` | not written yet |
| `Argument_cannot_be_used_in_lookup_table` of `Simplify_switch_expr.v` | `Simplify_switch_expr.Argument_cannot_be_used_in_lookup_table` | not written yet |
| `Empty` of `decl/Queue.v` | `Queue.Empty` | not written yet |
| `Invalid_argument` of `decl/Stdlib_.v` | `Invalid_argument` | not written yet |

A contract of a name is written when a proof first needs it.

WHAT STAYS TRUSTED ABOUT NAMES. No tool reads a contract of a name.

- That the name in the contract is the one that the rule gives, and that
  the declaration's `Extract Inlined Constant` names the same exception of
  OCaml.
- That two exceptions of OCaml never get one name. The rule gives that for
  an exception that is defined once, at the top level of a file or of a
  plain module of it: two files of a program have two names, and so have
  two modules of a file. The eight above are such (read in the compiler's
  files). It does NOT give it for an exception that a functor's body, a
  local module or a `let exception` defines: OCaml makes a new exception
  there each time, and one name would stand for all of them. Such an
  exception must not be declared in this form.
- That an exception carries what its declaration says. An exception can be
  USED only if it carries `unit` or `string`: Rocq refuses the others
  (`monad/real/Kit_refuses.v`), and `make exceptions` refuses their
  declaration, by the spelling of the type (a file that gave the name
  `unit` or `string` to another type would pass that tool; none does).

## The contracts of today

| contract | file | of | what it says |
|---|---|---|---|
| `prints_or_fatal format args` | `contracts/Port_monad.v` | the kit's `print_fatal_message` | the printing of the fatal error with this format and these arguments returns, or ends in a fatal error |
| `fatal_error_prints` | `contracts/Port_monad.v` | the same | the same of every `Misc.fatal_error msg` (the format `%s`) |
| `raise_with_backtrace_raises` | `contracts/Printexc.v` | `Printexc.raise_with_backtrace` | it does not return; if it raises, it raises the value that it is given; nothing of the state after it |
| `get_raw_backtrace_returns` | `contracts/Printexc.v` | `Printexc.get_raw_backtrace` | it returns, or ends in a fatal error |
| `Invalid_apply_cont_named` | `contracts/Unboxing_epa.v` | `Invalid_apply_cont` of `decl/Unboxing_epa.v` | its name |
| `Simple_not_in_scope_named` | `contracts/ported/Simplify_simple.v` | `Simple_not_in_scope` of `Simplify_simple.v` | its name |
| `Invalid_apply_cont_named`, `Prevent_current_unboxing_named` | `contracts/ported/unboxing/Unboxing_epa.v` | the two exceptions of `unboxing/Unboxing_epa.v` | their names |

WHAT FOLLOWS WITHOUT A CONTRACT (`Kit_laws.v`): a fatal error never
returns, whatever its printing does; a handler for an exception takes what
a raise of that exception raises; a handler for an exception of the kit
lets another exception of the kit pass.

## A fatal error that ends in a fatal error

`Misc.fatal_errorf` prints before it raises, and the printing runs the
printers that the message is given. The printing is a parameter of the kit.
So that `fatal_errorfN ..` ENDS IN A FATAL ERROR, and not in an exception
of a printer, is the contract `prints_or_fatal` of that message
(`fatal_errorf_args_fatal_only`). It is a contract of ONE message with its
arguments: the kit does not know which arguments are printers.

## The handlers that print a context and raise the fatal error again

Four functions of the port handle `Misc.Fatal_error`, print a context and
raise the fatal error again with `Printexc.raise_with_backtrace`. THE
CONTRACT `raise_with_backtrace_raises` ALONE GIVES ONLY THIS: the handler
never returns. So what the function returns, its body returned
(`add_use_returns` in `proofs/env/Continuation_uses_handlers.v`). It does
not give that the function ends in a fatal error when its body does: before
the handler raises again it calls declared functions, and one of them could
raise another exception. For "returns, or ends in a fatal error" a proof
needs, of each handler, the two contracts of `contracts/Printexc.v` and
that each call of the handler returns or ends in a fatal error:

| function | the calls of its handler, besides the two of `Printexc` |
|---|---|
| `simplify_named0` of `Simplify_named.v` (around `simplify_static_consts`) | `Format.eprintf6` with that format and the printers `Flambda_colours.error`, `Flambda_colours.pop`, `Bound_static.print`, `DA.print` |
| `simplify_named` of `Simplify_named.v` | `Format.eprintf8` with that format and the printers `Flambda_colours.error`, `Flambda_colours.pop`, `Bound_pattern.print`, `Named.print`, `DA.print` |
| `simplify_function_body` of `Simplify_set_of_closures.v` | `Format.eprintf16` with that format and the printers `Flambda_colours.error`, `Flambda_colours.pop`, `Format.pp_print_option None Function_slot.print`, `Bound_parameters.print`, `Continuation.print`, `Variable_.print`, `Expr.print`, `DA.print` |
| `add_use` of `env/Continuation_uses.v` | `U.env_at_use use`; `U.arg_types use`; `Format.eprintf10` with that format and the printers `Flambda_colours.error`, `Flambda_colours.pop`, `Continuation.print`, `Format.pp_print_list (Some Format.pp_print_space) T.print`, the file's own `print`, `DE.print` |

For `add_use` this is a theorem: `add_use_fatal_only` in
`proofs/env/Continuation_uses_handlers.v`. Its premises are the two
contracts and six more: of these three calls and of the four calls of the
body (`U.arg_types use` is called in both, and has one premise). For the
other three functions the row is a reading of the handler's text; no
theorem about them is proved yet, and their bodies need premises of their
own.

A fifth handler raises by the kit's own `raise_`: the one of
`make_optimistic_fields` in `unboxing/Optimistic_unboxing_decision.v`. It
needs no contract of `Printexc`; it needs that its call of `Format.eprintf6`
(with the printers `T.print`, `T.print`, `TE.print`) returns or ends in a
fatal error.
