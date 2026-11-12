#!/usr/bin/env python3
"""Checks the table of C functions of FlambdaExtcallSpec.v against the C
functions themselves. It goes with the work of P1 and is not part of any
build.

    P1-extcall.py ocaml > extcall_check.ml
        An OCaml program that calls each of the fourteen C functions, by
        its name in the runtime, on every pair of a list of strings and
        on every pair of a list of integers, and prints what each
        returns. The arguments go through [Sys.opaque_identity], so that
        the compiler calls the C function and computes nothing itself.
        For the integers it also prints what the same comparison gives
        in a function whose parameters have the type [int], which is
        where Simplify replaces the call by a primitive.
    P1-extcall.py rocq < output > ExtcallCheck.v
        From what that program printed, a Rocq file with one example:
        that [eval_extcall] gives the same answer on every line. It is
        compiled with the library of the model in scope (-Q, as
        rocq/Makefile does). The output must be exactly the lines that
        the program makes, each once: a line that is missing, repeated,
        unknown or malformed is an error, so that an empty or a cut
        output proves nothing.

The program is to be compiled by the compiler built from the tree and
run; the Rocq file is to be compiled, and not kept."""
import sys

STRINGS = [b"", b"a", b"b", b"ab", b"abc", b"abd", b"ab\x00", b"\x00",
           b"\x00\x00", b"a\x00b", b"\x7f", b"\x80", b"\xff", b"\xff\x00",
           b"1234567", b"12345678", b"123456789", b"12345678\x00",
           b"hello, world", b"hello, worle", b"hello, worl"]
MIN, MAX = -(1 << 62), (1 << 62) - 1
INTEGERS = [MIN, MIN + 1, -256, -2, -1, 0, 1, 2, 255, 256, MAX - 1, MAX]
COMPARISONS = ["compare", "equal", "notequal", "lessthan", "lessequal",
               "greaterthan", "greaterequal"]

def ocaml_string(s):
    return '"' + "".join("\\%03d" % b for b in s) + '"'

def ocaml():
    out = []
    for c in COMPARISONS:
        result = "int" if c == "compare" else "bool"
        out.append('external string_%s : string -> string -> %s = '
                   '"caml_string_%s"' % (c, result, c))
        out.append('external poly_%s : \'a -> \'a -> %s = "caml_%s"'
                   % (c, result, c))
        out.append("let[@inline never] int_%s (x : int) (y : int) = "
                   "poly_%s x y" % (c, c))
    out.append("let o = Sys.opaque_identity")
    out.append("let b x = if x then 1 else 0")
    out.append("let strings = [| %s |]"
               % "; ".join(ocaml_string(s) for s in STRINGS))
    out.append("let integers = [| %s |]"
               % "; ".join("(%d)" % i for i in INTEGERS))
    out.append("let () =")
    out.append("  Array.iteri (fun i s1 -> Array.iteri (fun j s2 ->")
    for n, c in enumerate(COMPARISONS):
        conv = "" if c == "compare" else "b "
        out.append('    Printf.printf "S %d %%d %%d %%d\\n" i j '
                   "(%s(string_%s (o s1) (o s2)));" % (n, conv, c))
        out.append('    Printf.printf "P %d %%d %%d %%d\\n" i j '
                   "(%s(poly_%s (o s1) (o s2)));" % (n, conv, c))
    out.append("    ()) strings) strings;")
    out.append("  Array.iteri (fun i x -> Array.iteri (fun j y ->")
    for n, c in enumerate(COMPARISONS):
        conv = "" if c == "compare" else "b "
        out.append('    Printf.printf "I %d %%d %%d %%d %%d\\n" i j '
                   "(%s(poly_%s (o x) (o y))) (%s(int_%s (o x) (o y)));"
                   % (n, conv, c, conv, c))
    out.append("    ()) integers) integers")
    print("\n".join(out))

CONSTRUCTORS = ["Cmp_compare", "Cmp_equal", "Cmp_notequal", "Cmp_lessthan",
                "Cmp_lessequal", "Cmp_greaterthan", "Cmp_greaterequal"]

def expected_rows():
    rows = set()
    for c in range(len(COMPARISONS)):
        for i in range(len(STRINGS)):
            for j in range(len(STRINGS)):
                rows.add(("S", c, i, j))
                rows.add(("P", c, i, j))
        for i in range(len(INTEGERS)):
            for j in range(len(INTEGERS)):
                rows.add(("I", c, i, j))
    return rows

def rocq():
    checks = []
    disagreements = 0
    expected = expected_rows()
    seen = set()
    for number, line in enumerate(sys.stdin, 1):
        fields = line.split()
        try:
            kind = fields[0]
            c, i, j, answer = (int(f) for f in fields[1:5])
            row = (kind, c, i, j)
            if len(fields) != (6 if kind == "I" else 5):
                raise ValueError
            if row not in expected:
                raise ValueError
            if answer not in ((-1, 0, 1) if c == 0 else (0, 1)):
                raise ValueError
        except (IndexError, ValueError):
            sys.exit("line %d is not a line of the program: %r"
                     % (number, line))
        if row in seen:
            sys.exit("line %d repeats a comparison: %r" % (number, line))
        seen.add(row)
        if kind == "S":
            checks.append("(Caml_string_comparison %s, str %d, str %d, %d)"
                          % (CONSTRUCTORS[c], i + 1, j + 1, answer))
        elif kind == "P":
            checks.append("(Caml_comparison %s, str %d, str %d, %d)"
                          % (CONSTRUCTORS[c], i + 1, j + 1, answer))
        else:
            if int(fields[5]) != answer:
                disagreements += 1
            checks.append("(Caml_comparison %s, int (%d), int (%d), %d)"
                          % (CONSTRUCTORS[c], INTEGERS[i], INTEGERS[j],
                             answer))
    if seen != expected:
        sys.exit("%d comparisons are missing of the %d that the program "
                 "makes" % (len(expected - seen), len(expected)))
    if disagreements:
        sys.exit("%d comparisons of integers differ between the C function "
                 "and the function at type int" % disagreements)
    print("From Stdlib Require Import ZArith List Bool.")
    print("From OxCamlFlambda2 Require Import FlambdaModel FlambdaValueSpec")
    print("  FlambdaPrimitiveModel FlambdaPrimitiveSpec FlambdaExtcallSpec.")
    print("Import ListNotations.")
    print("Local Open Scope Z_scope.")
    print("Definition statics : static_env :=")
    print("  Static_env []")
    print("    [%s]."
          % ";\n     ".join("(%d%%positive, Static_string [%s])"
                            % (n + 1, "; ".join(str(b) for b in s))
                            for n, s in enumerate(STRINGS)))
    print("Definition str (s : positive) : value := Value_symbol s.")
    print("Definition int (i : Z) : value :=")
    print("  Value_const (Tagged_immediate i).")
    print("Definition agrees (check : extcall * value * value * Z) : bool :=")
    print("  let '(f, v1, v2, answer) := check in")
    print("  match eval_extcall statics f [v1; v2] with")
    print("  | Some (Value_const (Tagged_immediate i)) => i =? answer")
    print("  | _ => false")
    print("  end.")
    print("Definition checks : list (extcall * value * value * Z) :=")
    print("  [%s]." % ";\n   ".join(checks))
    print("Example the_table_agrees_with_the_runtime :")
    print("  forallb agrees checks = true.")
    print("Proof. vm_compute. reflexivity. Qed.")
    print("(* %d checks *)" % len(checks))

if len(sys.argv) > 1 and sys.argv[1] == "ocaml":
    ocaml()
elif len(sys.argv) > 1 and sys.argv[1] == "rocq":
    rocq()
else:
    sys.exit(__doc__)
