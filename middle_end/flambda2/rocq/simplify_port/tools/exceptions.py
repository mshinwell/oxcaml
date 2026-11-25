#!/usr/bin/env python3
#******************************************************************************
#*                                  OxCaml                                    *
#* -------------------------------------------------------------------------- *
#*                               MIT License                                  *
#*                                                                            *
#* Copyright (c) 2026 Jane Street Group LLC                                   *
#* opensource-contacts@janestreet.com                                         *
#*                                                                            *
#* Permission is hereby granted, free of charge, to any person obtaining a    *
#* copy of this software and associated documentation files (the "Software"), *
#* to deal in the Software without restriction, including without limitation  *
#* the rights to use, copy, modify, merge, publish, distribute, sublicense,   *
#* and/or sell copies of the Software, and to permit persons to whom the      *
#* Software is furnished to do so, subject to the following conditions:       *
#*                                                                            *
#* The above copyright notice and this permission notice shall be included    *
#* in all copies or substantial portions of the Software.                     *
#*                                                                            *
#* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *
#* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *
#* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *
#* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *
#* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *
#* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *
#* DEALINGS IN THE SOFTWARE.                                                  *
#******************************************************************************

"""exceptions.py KIT FILE.v ... : what a declared exception may carry
(GUIDE.md, section 4), as text. Also: exceptions.py --self-test.

In the real kit (KIT: monad/real/Port_monad.v) an exception is its name, and
what it carries is carried in the way of its TYPE: the class [Carried] has
one instance for each type that an exception can carry. The tool reads these
types from the text of KIT, in the sentences [Instance NAME : Carried T :=].
Then, in each FILE.v (the files of decl/ and the ported files), with the
comments and the strings taken out:

  1. a sentence that has the word [exception] must be
         Parameter NAME : exception T.
     with T one of those types. Any other sentence with that word is
     refused: the tool does not know what it declares (an [Axiom], a second
     name in one sentence, a function that gives an exception, an
     abbreviation of the type);
  2. the words of the class ([Carried], [Make_carried], [exn_carry],
     [exn_carried], [exn_carried_carry]) must not stand in the file. Only
     the kit makes an instance: with a second instance for one type, two
     files could carry that type in two ways, and a handler of the one
     would not take what the other raises.

WHAT IT DOES NOT SEE.
- An exception or an instance that is declared without these words: by a
  notation, or through a name that a file which the tool is not given
  makes for the type or for the class (the kit, contracts/, proofs/).
- Whether the OCaml text of the directive after the declaration makes and
  tests an exception that carries T: tools/declgen/check_realisations.py
  types the pair of a declaration of decl/, and [make given] compares the
  pair of a ported file with its form; neither compares it with T.
- The name of the exception (contracts/README.md).
- Rocq. In the real build Rocq itself refuses to raise, to make a value of
  or to handle an exception whose type has no instance
  (monad/real/Kit_refuses.v). So point 1 says early, and for a declaration
  that nothing uses yet, what Rocq says at the first use; the identity
  build takes any type.

The exit status is 1 if it said anything. It reads nothing that Rocq or
OCaml makes. It follows no file of the compiler."""
import re, sys

CLASS_WORDS = ("Carried", "Make_carried", "exn_carry", "exn_carried",
               "exn_carried_carry")


def strip(s):
    """The text with each comment and each string made blank (a string keeps
    its two quotes); the line breaks stay, so that a place is a line."""
    out = []; depth = 0; i = 0; n = len(s)
    while i < n:
        if s.startswith("(*", i):
            depth += 1; out.append("  "); i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; out.append("  "); i += 2; continue
        if s[i] == '"':
            # a string, also inside a comment (Rocq reads it there too): a
            # doubled quote inside it is one quote of the string
            j = i + 1
            while j < n:
                if s[j] == '"':
                    if s.startswith('""', j): j += 2; continue
                    break
                j += 1
            body = s[i + 1:j]
            out.append(('"' if depth == 0 else " ")
                       + "".join("\n" if c == "\n" else " " for c in body)
                       + ('"' if depth == 0 else " "))
            i = j + 1; continue
        out.append(s[i] if depth == 0 or s[i] == "\n" else " "); i += 1
    return "".join(out)


def sentences(text):
    """(line, sentence) for each sentence of a stripped text: it ends at a
    full stop that white space or the end of the text follows."""
    start = 0
    for m in re.finditer(r"\.(?=\s|$)", text):
        s = text[start:m.end()]
        line = text.count("\n", 0, start + len(s) - len(s.lstrip())) + 1
        yield line, " ".join(s.split())
        start = m.end()
    rest = text[start:]
    if rest.strip():
        line = text.count("\n", 0, start + len(rest) - len(rest.lstrip())) + 1
        yield line, " ".join(rest.split())


def word(w):
    return re.compile(r"(?<![A-Za-z0-9_'])%s(?![A-Za-z0-9_'])" % re.escape(w))


EXCEPTION = word("exception")
DECLARATION = re.compile(
    r"Parameter ([A-Za-z_][A-Za-z0-9_']*) : exception (.+?) ?\.")
INSTANCE = re.compile(
    r"(?:#\[[a-z, ]*\] ?)?Instance [A-Za-z_][A-Za-z0-9_']* : Carried (.+?) ?:=")


def plain(t):
    """A type with the brackets around the whole of it taken off."""
    t = t.strip()
    while t.startswith("(") and t.endswith(")"):
        depth = 0
        for k, c in enumerate(t):
            depth += c == "("; depth -= c == ")"
            if depth == 0 and k < len(t) - 1: return t
        t = t[1:-1].strip()
    return t


def carried_types(kit_text):
    """The types that the kit has an instance of [Carried] for."""
    types = []
    for _, s in sentences(strip(kit_text)):
        m = INSTANCE.match(s)
        if m: types.append(plain(m.group(1)))
    return types


def check(name, text, types):
    """The complaints about one file, as lines of text."""
    said = []
    for line, s in sentences(strip(text)):
        if EXCEPTION.search(s):
            m = DECLARATION.fullmatch(s)
            if not m:
                said.append("%s:%d: a sentence with the word [exception] that "
                            "is not [Parameter NAME : exception T.]: %s"
                            % (name, line, s[:120]))
            elif plain(m.group(2)) not in types:
                said.append("%s:%d: the exception %s carries [%s], which the "
                            "kit has no instance of [Carried] for (it has: %s)"
                            % (name, line, m.group(1), plain(m.group(2)),
                               ", ".join(types)))
        for w in CLASS_WORDS:
            if word(w).search(s):
                said.append("%s:%d: the word [%s] of the kit's class of what "
                            "an exception carries: only the kit makes an "
                            "instance" % (name, line, w))
    return said


# Made-up texts and the number of complaints that each must draw.
SELF_TEST_KIT = """
Class Carried (P : Type) : Type := Make_carried { exn_carry : P -> nat }.
#[export] Instance Carried_unit : Carried unit := {| exn_carry := 0 |}.
#[export] Instance Carried_string : Carried string :=
  {| exn_carry := 1 |}.
"""
SELF_TEST = [
    ("Parameter E : exception unit.\nExtract Inlined Constant E => "
     "\"((fun () -> E), (function E -> Some () | _ -> None))\".", 0),
    ("  Parameter E : exception\n    string.", 0),
    ("Parameter E : exception (unit).", 0),
    # THE FAULT: a type that the kit has no instance for
    ("Parameter E : exception (int * int).", 1),
    ("Parameter E : exception (exn_payload -> bool).", 1),
    ("Parameter E : exception Simple.t.", 1),
    # declarations that the tool does not know
    ("Axiom E : exception unit.", 1),
    ("Parameter E F : exception unit.", 1),
    ("Parameter make : string -> exception unit.", 1),
    ("Definition my_exception : Type := exception (int * int).\n"
     "Parameter E : my_exception.", 1),
    # the word inside a comment or a string is no declaration
    ("(* exception E of int * int (* and Carried *) *)\nDefinition x := 1.",
     0),
    ("(*OCAML\nexception E of (int * int)\nOCAML*)\n"
     "Parameter E : exception unit.", 0),
    ("Definition s : string := \"an exception (int * int)\".", 0),
    ("Definition exception_of_x := 1.", 0),
    # a second instance of the class
    ("Instance Mine : Carried unit := {| exn_carry := 2 |}.", 2),
    ("Parameter C : Carried (int * int).", 1),
]


def self_test():
    types = carried_types(SELF_TEST_KIT)
    bad = 0
    if types != ["unit", "string"]:
        print("exceptions --self-test: the instances read are %s" % types)
        bad += 1
    for text, want in SELF_TEST:
        got = check("made-up", text, types)
        if len(got) != want:
            bad += 1
            print("exceptions --self-test: %d complaints where %d are wanted "
                  "for: %s" % (len(got), want, text))
            for g in got: print("    " + g)
    faults = sum(1 for _, want in SELF_TEST if want)
    if bad == 0:
        print("exceptions --self-test: %d made-up texts, %d of them with a "
              "fault: each fault is caught, and nothing else is said"
              % (len(SELF_TEST), faults))
    return bad


def main():
    if sys.argv[1:] == ["--self-test"]:
        sys.exit(1 if self_test() else 0)
    if len(sys.argv) < 3:
        sys.exit("usage: exceptions.py KIT FILE.v ... | "
                 "exceptions.py --self-test")
    kit, files = sys.argv[1], sys.argv[2:]
    types = carried_types(open(kit).read())
    if not types:
        sys.exit("exceptions: no sentence [Instance NAME : Carried T :=] in %s"
                 % kit)
    said = []; declared = 0
    for f in files:
        text = open(f).read()
        # a file without these words has nothing for the tool
        if "exception" not in text and not any(w in text for w in CLASS_WORDS):
            continue
        got = check(f, text, types)
        said += got
        declared += sum(1 for _, s in sentences(strip(text))
                        if DECLARATION.fullmatch(s))
    for line in said: print(line)
    if not said: verdict = "nothing wrong"
    elif len(said) == 1: verdict = "1 thing wrong"
    else: verdict = "%d things wrong" % len(said)
    print("exceptions: %d files read; %d declared exceptions; the types that "
          "an exception can carry (%s): %s; %s"
          % (len(files), declared, kit, ", ".join(types), verdict))
    sys.exit(1 if said else 0)


main()
