# P1: calls of C functions in the model. A request

Owner: P1. For the human and for C0, whose files the change would be
in. Nothing here is done. With the loads from strings in, the next
thing a plain program on strings meets is not a primitive: it is a
call of a C function. This says which calls the front end makes, what
Simplify does with them, and two ways to give them a meaning.

## What there is

An `Apply` whose call kind is `C_call` is refused by the conversion
(the unit is "not checked"). A unit with one that `-drawfexpr` prints
does not even parse back (`requests/V2-missing-constructs.md`, items
10 and 4).

## The calls that the front end makes of plain OCaml

Tried on the compiler built from this tree, each from a few lines of
source with no library:

| Source | Call | Allocates |
|--------|------|-----------|
| `match s with "a" -> ... \| "bc" -> ...` on a string | `caml_string_notequal`, and `caml_string_compare` for a match with many cases | no |
| `=` and `<>` at type `string` | `caml_string_equal`, `caml_string_notequal` | no |
| `<`, `<=`, `>`, `>=`, `compare` at type `string` | `caml_string_lessthan` and the like, `caml_string_compare` | no |
| `=`, `<`, `compare` and the like at a type that is not known to be `int` | `caml_equal`, `caml_lessthan`, `caml_compare` and the like | may raise |
| `exception E` | `caml_fresh_oo_id` | no; has an effect |

With a library there are many more (output, `caml_array_make`,
conversions between numbers and strings). The first three rows are
pure functions of two immutable strings.

## What Simplify does with a C call

`simplify/simplify_extcall.ml`. It knows eight names. For
`caml_compare`, `caml_equal`, `caml_notequal`, `caml_lessequal`,
`caml_lessthan`, `caml_greaterequal` and `caml_greaterthan`: where
the types prove that both arguments are tagged immediates, the call
becomes `Int_comp` at the tagged immediates (`Phys_equal` for the two
equalities) and a `Tag_immediate`; where they prove that both are
boxed numbers of one kind, two `Unbox_number`, the comparison at that
kind and a `Tag_immediate`. For `caml_array_make` it gives the result
a type. Every other call is left as it is, with a result of unknown
type. So a model in which these seven have no meaning cannot check
those rewrites, and one in which they have a meaning has to agree
with the integer comparisons on immediates and on boxed integers.

## Two ways

- (A) A table of known functions. The machine has, for some names, a
  function from the values of the arguments to a result, and an
  `Apply` of such a name goes to the return continuation with it. The
  conversion still refuses a call of a name that is not in the table.
  First in the table: the seven comparisons of strings, which are
  total on two strings (`runtime/str.c`: the bytes are compared as
  `memcmp` does up to the shorter length, then the lengths; the
  results are -1, 0 and 1, or a boolean). Then the seven polymorphic
  comparisons on what Simplify specialises (two tagged immediates;
  two boxed integers of one kind; floats when the model has them),
  and, if wanted, on strings and on immutable blocks by structure.
  Where the table gives no result the call is undefined, with a CR:
  on a closure the real function raises, and between values of
  different shapes it follows the layout of the runtime.
- (B) Calls as events. A run is observed by the calls it makes (the
  name and the arguments) as well as by how it ends, and the result
  of a call is given by the environment. This covers every call at
  once, and is what a statement about whole programs needs in the
  end. It makes the machine depend on an environment, it needs the
  heap to say what of the arguments is observed and what a call may
  change, and Simplify's seven rewrites still need (A) for those
  names.

## Recommendation

(A), in two steps, each small. First the seven comparisons of
strings: with them, a `match` on a string and the equality of two
strings are converted and run. Second the seven polymorphic
comparisons on immediates and boxed integers, so that the rewrites of
`simplify_extcall.ml` can be checked (they are a pass for the
validator, like the identities of arithmetic). `caml_fresh_oo_id`
waits for the heap, which has identities. (B) is for later, with the
whole-program statement.

The change is in the core: a case of the machine for an `Apply` with
a C call, the well-formedness of such an `Apply`, and the conversion.
What each function computes can be leaf work beside the primitives,
with the same laws (a result is in range, is kept when the static
environment grows, and is read through the observations).

Asked of the human: (A) or (B) first; whether a call the table has no
result for is undefined or stops the check; whether polymorphic
comparison by structure is wanted now or only what Simplify
specialises.
