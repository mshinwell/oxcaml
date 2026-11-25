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


"""given.py : the OCaml text that the ported files give, against the
compiler's files (GUIDE.md, sections 4 and 5). It follows no file of the
compiler.

    given.py FILE.v ...      (the Makefile's target given, a part of check)

Rocq prints most of an extracted file from the Rocq definitions of
DIR/Foo.v. The rest is OCaml text that Foo.v GIVES, and that Rocq copies
without reading it:

- a BLOCK: the lines between a line (*OCAML and a line OCAML*), which
  tools/assemble.sh copies to the head of the extracted file, or between
  (*OCAML-END and OCAML-END*), which it copies to the end;
- the STRINGS OF A DIRECTIVE of the extraction, in one of three forms
  (the strings before => and the last one may be absent):
      Extract Constant NAME "'a" .. => "TEXT".
      Extract Inlined Constant NAME => "TEXT".
      Extract Inductive NAME => "T" [ "C1" .. "Cn" ] "MATCH".

Foo.v follows middle_end/flambda2/simplify/DIR/foo.ml, its DONOR. For each
given text the tool looks for one of three RELATIONS to the donor that it
can check (R1, R2, R3, below); or the text is of a NAMED CLASS that needs
no donor; or a MARK stands over it. THE RULE:

- a text that holds no relation, is of no class and has no mark over it
  is an error;
- a mark verbatim, type or update is an error if EVERY text under it
  holds a relation or is of a class: the mark is not needed, a note of
  lines is enough;
- a note of lines that is not right is an error where the tool can tell:
  the text stands at other lines of the donor;
- so are a sentence that has the word Extract or Extraction and is none
  of the three forms (also one of them after an attribute), a block that
  is not a comment of its own between two sentences, and a block that
  does not end.

The tool prints the errors and then one line of numbers; its exit status
is 1 if there is an error. With GIVEN_ALL in the environment it first
prints one line for each text: the relation that holds, with each
DIFFERENCE (D1 to D5, below) that was used, or why nothing holds; and the
marks over it.

EVERYTHING IS COMPARED AS WORDS: the tokens of OCaml, in order. White
space, line breaks and comments between the tokens are not compared. A
string is one token with all its characters: the white space INSIDE a
string of a given text is compared with the donor's.

THE TOKENS are read by this file, not by the compiler's lexer. For each
donor, decl/DONOR-TOKENS.tsv has a CHECKSUM: the MD5 of the characters
that are not white space, in the tokens that the compiler's own lexer
read in the donor, comments left out (tools/declgen/donors.ml). At each
run the tool wants the same checksum for its own tokens of that donor.
That shows that the tool reads the same characters that are not white
space, outside comments, as the compiler's lexer. It is no identity of
the tokens or of the source: it does not show that the two lexers cut the
characters into the same tokens (they do not: a label, an attribute, a
type variable), and it says nothing of the white space inside a string,
which it leaves out on both sides. If the checksum differs (the donor
has changed, or the tool misreads it), or one of the two tables of decl/
is not there or has rows of another width, that is an error, and no text
of the file holds R1, R2 or R3. The given text itself, in the .v, is
read by the tool's tokens only.

THE NOTE OF LINES is a comment of the ported file that has lines of the
donor and nothing before them: (* 12 *), (* 12-20 *), (* 12-20 and 43 *),
(* 3, 7 and 9-11 *); words may follow a full stop: (* 12-20. Words. *).

THE GROUPS say which note and which marks stand over a text. They are
read in the order of the file, from what stands outside the sentences:
- a note of lines begins a group;
- a mark (* PORT-GAP(kind): words *) joins the group if only comments
  stand between it and the note or the mark before it; else it begins a
  group. If its words begin with lines, those are the lines of the group
  from there on;
- a given text is of the group that is open: it has the lines and all the
  marks of the group;
- another comment closes the group if the group has a text already;
  before the first text it changes nothing (the words of a mark that has
  gone, the donor's own comment);
- a sentence closes the group, unless it has no body of ported code:
  From, Require, Import, Arguments, Open Scope, Inductive, Record,
  Parameter, [Module A := P], and a [Definition NAME] that the directive
  [Extract Constant NAME] or [Extract Inlined Constant NAME] follows.
A mark inside a sentence (at a use) stands over no text.

R1, THE DONOR'S LINES. The tokens of the text are the tokens that BEGIN on
the lines that the note names: all of them, in the order in which the note
names the lines.
- A block: the whole block.
- Extract Constant NAME => "TEXT". Rocq prints [type NAME = TEXT] for a
  type (the parameters before NAME) and [let NAME = TEXT] for a value. One
  of these two must be the donor's lines: the directive holds what follows
  the [=] (D1). No other keyword holds ([and], [type nonrec], [let rec]:
  Rocq prints none of them). The Rocq name may have [_] at its end where
  the donor's name has none (D5). Or TEXT begins [() include] or [()
  module], and what follows [()] is the donor's lines (D2: Rocq prints
  [let NAME = ()], and OCaml reads the item after it).
- Extract Inlined Constant NAME => "TEXT" that is no setter and of no
  class: for EACH line or range that the note names, TEXT is all that the
  donor has there (an expression that has its lines to itself).
If a block or an Extract Constant does not hold at the lines of its note
(or has no note) and its text stands elsewhere in the donor, that is an
error, which names those lines.

R2, A SETTER OF A RECORD UPDATE. Extract Inlined Constant update_X => "(fun
t p1 .. pn -> { t with F1 = p1; ..; Fn = pn })": one field for each
parameter, in order (a field may have its module before it). The note
names PLACES of the donor. decl/UPDATES.tsv has every record update of
the typed tree of the donor: the lines where it begins and ends, the
fields that it gives in the order of the text, the place of its record
type, and all the fields of that type (tools/declgen/donors.ml). The tool
wants:
- at each line N that the note names, a record update of the donor that
  begins there and gives exactly F1 .. Fn, in that order. Named as N-M, it
  ends at M; named by N alone, it may go on over more lines (D3);
- all these updates are of ONE record type (one place of the type);
- EVERY update of the donor that is of that type and gives exactly those
  fields is named;
- the sentence before the directive is [Definition update_X .. := {| G :=
  .. ; .. |}], and its record has the fields of that type, all of them, in
  the order of the type (a [_] at the end of a Rocq field is left out, and
  so are the modules before it).
That the Definition gives each field of the text its parameter and keeps
every other field is the check of tools/lint.py. If the table says that
the typed tree of the donor was not read, no setter of the file holds.

R3, THE FORM OF A TYPE. The strings of Extract Inductive NAME => "T" [ ..
] "MATCH" are NOT the compiler's text: no file of the compiler has them.
They are THE ONE FORM that follows mechanically from the OCaml definition
of the type T (tools/declgen/emit_types.ml writes the same form for a type
of decl/). The tool makes the form again from the definition and compares
it word for word.
THE DEFINITION is taken from the ported file itself, and only from a text
that holds R1: a block (for a directive outside the Rocq modules of the
file, or for a name M.T), or the directive Extract Constant of a type in
the same Rocq module (with the types that follow in it after [and]).
Where the definition of a type does not hold R1, its strings cannot hold
R3. Nor can those of a type that is written out in the directive
(polymorphic variants, a tuple with labels), of a name of which the file
gives two definitions, or of a directive inside a Rocq functor. The
definition is a variant or a record.
THE FORM, with x__1, x__2 .. for the arguments, f__1 .. for the cases and
x__0 for the value (a constructor of a type M.T is written M.C):
- a constructor without arguments: C, or (C : T);
- with arguments: C, or (fun x__1 -> (C x__1 : T)), (fun (x__1, x__2) ->
  (C (x__1, x__2) : T));
- with an inline record: (fun (x__1, x__2) -> (C { f = x__1; g = x__2 } :
  T)), the fields in the order of the definition;
- MATCH: (fun f__1 .. f__k x__0 -> match (x__0 : T) with C x__1 -> f__1
  x__1 | D -> f__2 () | ..), the constructors in the order of the
  definition. It may be absent if no string is a function;
- a record: one string, (fun (x__1, .., x__n) -> ({ f1 = x__1; .. } :
  T)), and MATCH is (fun f__1 x__0 -> let ({ f1 = x__1; .. } : T) = x__0
  in f__1 x__1 .. x__n).
The type of an annotation is not compared (D4): where the form has [(E :
T)], a string may have [E], or [(E : U)] with a type U written otherwise
(another name of the type, [_ T] for a type with a parameter).
THE ROCQ TYPE: the nearest [Inductive] or [Record] NAME before the
directive stands in the same module and has as many constructors as the
definition, each with as many arguments as the constructor of the
definition has arguments or fields (for a record: as many arguments, or
fields, as the record has fields).
Also R3, an Extract Inlined Constant NAME => "TEXT" for a record T whose
definition the file gives in that way:
- the reader of a field: (fun (x__0 : T) -> x__0.f), where f is a field of
  T, and NAME is f (it may have [_] at its end);
- the maker: (fun x__1 .. x__n -> ({ f1 = x__1; .. } : T));
- the eliminator: (fun x__0 f__1 -> let ({ f1 = x__1; .. } : T) = x__0 in
  f__1 x__1 .. x__n).

THE NAMED CLASSES, each an Extract Inlined Constant NAME => "TEXT":
- ITS OWN NAME: TEXT is NAME; or NAME without the [_] at its end; or a
  path M.f where NAME is M_f (D5);
- THE PAIR OF AN EXCEPTION: ((fun () -> NAME), (function NAME -> Some () |
  _ -> None));
- A NUMBER: TEXT is one number of OCaml as the tool's tokens read one (an
  integer in base ten, sixteen, eight or two, with or without the letter
  of its size; a float, with or without digits after its point and an
  exponent), or such a number with [-] before it, in brackets. If the
  file has [Definition NAME : .. := N.], TEXT is an integer and the two
  numbers are equal (a float is equal to none). If it has none (NAME is a
  Parameter), the note names lines of the donor and the literal stands
  on each of them, as the same token.

THE DIFFERENCES, which the listing names at each text: D1 the directive
holds what follows [type NAME =] or [let NAME =]; D2 an item after [()];
D3 a place of a setter is named by the line where the update begins; D4
the type of an annotation in a string of a form; D5 a Rocq name with [_]
at its end, or with [_] for the dots of a path. NOT ALLOWED (such a text
keeps its mark): another order of the types of a recursive group; text
before the definition; a name that is changed inside a text.

THE MARKS that may stand over a given text: verbatim, type, update, init,
decl, unported. A text that holds nothing under one of them is counted in
the line of numbers, and the tool says nothing more of it. The other kinds
(loose, papp, record-order ..) are about ported code: they stand for no
text.

WHAT THE TOOL DOES NOT ESTABLISH.
- Anything about a text under a mark that stays.
- That the ported code USES a setter, a maker, a reader or a number where
  the donor has the update, the construction, the read or the number:
  only the given text is compared.
- Where a text stands in the extracted file, and so what its names mean
  there. A block goes to the head or to the end of the file and the text
  of a directive to the place of the Rocq definition; the donor may have
  the lines elsewhere (inside a module, inside a function). The tool does
  not read extracted/: OCaml's types check it (make check).
- That Rocq honours a directive (GUIDE.md, section 4: inside a Rocq
  functor it does not honour one on a Parameter, and says nothing).
- That the Rocq type has the arguments of a constructor in the order of
  the fields: their number is compared. OCaml's types see a swap only
  where the two fields have different types.
- That a note names ALL the donor's lines of a thing (a setter's note
  must): a note may name a part, and then the text is that part.
- It is no parser of OCaml and no reader of Rocq's terms. It reads
  tokens, brackets and the few forms above; the sentences and the modules
  of Rocq as tools/papp.py reads them (full stops, [Module] .. [End]); the
  definition of a type up to the next item at the same depth of brackets.
  It was held against the texts that the ported files have today: where
  one of them could pass falsely, the tool was changed. A file that is
  written to mislead it may pass (the number of [Definition NAME] is
  looked for by the name alone, in the whole file; a comment that looks
  like a note of lines is one): no ported file has such text, and that is
  a stated limit.
"""

import collections
import hashlib
import os
import re
import sys

sys.dont_write_bytecode = True
TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import papp

PORT = os.path.join(TOOLS, "..")
DECL = os.path.join(PORT, "decl")
REPO = os.path.join(PORT, "..", "..", "..", "..")
SIMPLIFY = "middle_end/flambda2/simplify"
# the kinds of marks that may stand over a given text; and those of them
# that are an error over texts that all hold
OVER = ("verbatim", "type", "update", "init", "decl", "unported")
JUDGED = ("verbatim", "type", "update")

# ---- the tokens of OCaml ------------------------------------------------

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
NUMBER = re.compile(
    r"0[xX][0-9a-fA-F_]+[lLn]?|0[oObB][0-9_]+[lLn]?"
    r"|[0-9][0-9_]*(?:\.[0-9_]*)?(?:[eE][+-]?[0-9_]+)?[lLn]?"
)
CHAR = re.compile(r"'(?:[^\\'\n]|\\(?:[\\'\"ntbr ]|[0-9]{3}|x[0-9a-fA-F]{2}|o[0-7]{3}))'")
QUOTED = re.compile(r"\{([a-z_]*)\|")
OPERATOR = re.compile(r"[!$%&*+\-./:<=>?@^|~#]+")
WHITE = re.compile(r"[ \t\n\r\x0c]")


def string_end(s, i):
    """After the string of OCaml that begins at the quote at i."""
    i += 1
    while i < len(s):
        if s[i] == "\\":
            i += 2
        elif s[i] == '"':
            return i + 1
        else:
            i += 1
    return len(s)


def tokens(s):
    """The tokens of an OCaml text, comments left out: (token, the line
    where it begins). A name, a number, a string, a character and a type
    variable are whole tokens; a run of operator characters is one token;
    every other character is a token by itself."""
    out = []
    i = 0
    n = len(s)
    line = 1
    while i < n:
        c = s[i]
        if c == "\n":
            line += 1
            i += 1
        elif c in " \t\r\x0c":
            i += 1
        elif s.startswith("(*", i) and not s.startswith("(*)", i):
            # a comment: comments inside it, and its strings, are read
            depth = 1
            i += 2
            while i < n and depth:
                if s.startswith("(*", i):
                    depth += 1
                    i += 2
                elif s.startswith("*)", i):
                    depth -= 1
                    i += 2
                elif s[i] == '"':
                    j = string_end(s, i)
                    line += s.count("\n", i, j)
                    i = j
                else:
                    if s[i] == "\n":
                        line += 1
                    i += 1
        elif c == '"':
            j = string_end(s, i)
            out.append((s[i:j], line))
            line += s.count("\n", i, j)
            i = j
        elif c == "{" and QUOTED.match(s, i):
            m = QUOTED.match(s, i)
            j = s.find("|" + m.group(1) + "}", m.end())
            j = n if j < 0 else j + len(m.group(1)) + 2
            out.append((s[i:j], line))
            line += s.count("\n", i, j)
            i = j
        elif c == "'" and CHAR.match(s, i):
            m = CHAR.match(s, i)
            out.append((m.group(0), line))
            i = m.end()
        elif c == "'" and IDENT.match(s, i + 1):
            m = IDENT.match(s, i + 1)
            out.append((s[i:m.end()], line))
            i = m.end()
        elif IDENT.match(s, i):
            m = IDENT.match(s, i)
            out.append((m.group(0), line))
            i = m.end()
        elif c.isdigit():
            m = NUMBER.match(s, i)
            out.append((m.group(0), line))
            i = m.end()
        elif OPERATOR.match(s, i):
            m = OPERATOR.match(s, i)
            out.append((m.group(0), line))
            i = m.end()
        else:
            out.append((c, line))
            i += 1
    return out


def words(s):
    return [t for t, _ in tokens(s)]


def digest(toks):
    """The checksum of the tokens: the MD5 of their characters that are
    not white space (inside a string too), with nothing between one token
    and the next. decl/DONOR-TOKENS.tsv has it for the tokens of the
    compiler's lexer."""
    chars = WHITE.sub("", "".join(t for t, _ in toks))
    return hashlib.md5(chars.encode("latin-1", "replace")).hexdigest()


# ---- the donors ---------------------------------------------------------

Update = collections.namedtuple("Update", "first last type place given all")


class Donor(object):
    """A file of the compiler that a ported file follows: its tokens, its
    record updates (decl/UPDATES.tsv), and why it is not read, if it is
    not."""

    def __init__(self, rel, text, digests, updates):
        self.rel = rel
        self.why = None
        self.updates = []
        self.no_updates = None
        self.tokens = []
        if text is None:
            self.why = "%s is not there" % rel
            return
        self.tokens = tokens(text)
        row = digests.get(rel)
        if row is None:
            self.why = "decl/DONOR-TOKENS.tsv has no row for %s" % rel
        elif row != digest(self.tokens):
            self.why = (
                "the tool does not read %s as the compiler's lexer did when decl/DONOR-TOKENS.tsv "
                "was made (another checksum of the characters that are not white space): the file has changed, "
                "or the tool misreads it" % rel
            )
        for f in updates.get(rel, []):
            if f[1] == "-":
                self.no_updates = f[3]
            else:
                self.updates.append(
                    Update(int(f[1]), int(f[2]), f[3], f[4], tuple(f[5].split()), tuple(f[6].split()))
                )

    def at(self, ranges):
        """The tokens of the lines of the ranges, in the order of the ranges."""
        out = []
        for a, b in ranges:
            out += [t for t, l in self.tokens if a <= l <= b]
        return out

    def find(self, toks):
        """The lines of each place where the tokens stand together."""
        if not toks:
            return []
        names = [t for t, _ in self.tokens]
        m = len(toks)
        first = toks[0]
        return [
            (self.tokens[i][1], self.tokens[i + m - 1][1])
            for i in range(len(names) - m + 1)
            if names[i] == first and names[i:i + m] == toks
        ]


TABLES = None
DONORS = {}


def read_tables():
    """The two tables of decl/, and what is wrong with them."""
    digests = {}
    updates = collections.defaultdict(list)
    wrong = []
    for name, cols in (("DONOR-TOKENS.tsv", 3), ("UPDATES.tsv", 7)):
        try:
            rows = open(os.path.join(DECL, name)).read().split("\n")
        except IOError:
            wrong.append("decl/%s is not there" % name)
            continue
        for row in rows:
            f = row.split("\t")
            if not row:
                continue
            if len(f) != cols:
                wrong.append("decl/%s has a row of %d columns, not %d: it is not the table of this tool" % (
                    name, len(f), cols))
                break
            if cols == 3:
                digests[f[0]] = f[2]
            else:
                updates[f[0]].append(f)
    return digests, updates, wrong


def donor_of(path):
    """The donor of the ported file DIR/Foo.v: SIMPLIFY/DIR/foo.ml."""
    global TABLES
    rel = os.path.relpath(os.path.abspath(path), os.path.abspath(PORT))
    rel = SIMPLIFY + "/" + os.path.join(os.path.dirname(rel), os.path.basename(rel)[:-2].lower() + ".ml")
    rel = rel.replace(os.sep, "/")
    if rel not in DONORS:
        if TABLES is None:
            TABLES = read_tables()
        try:
            text = open(os.path.join(REPO, rel), encoding="latin-1").read()
        except IOError:
            text = None
        DONORS[rel] = Donor(rel, text, TABLES[0], TABLES[1])
        if TABLES[2]:
            DONORS[rel].why = "; ".join(TABLES[2])
    return DONORS[rel]


def show(ranges):
    return ", ".join("%d" % a if a == b else "%d-%d" % (a, b) for a, b in ranges) or "none"


# ---- the ported file ----------------------------------------------------

RANGE = r"\d+(?:\s*-\s*\d+)?"
RANGES = r"%s(?:(?:\s*,\s*and\s+|\s*,\s*|\s+and\s+)%s)*" % (RANGE, RANGE)
NOTE = re.compile(r"\(\*\s*(%s)\s*(?:\.\s.*)?\*\)" % RANGES, re.S)
MARK = re.compile(r"\(\*\s*PORT-GAP\(([a-z-]+)\)\s*:?\s*(.*)\*\)", re.S)
FIRST_LINES = re.compile(r"(%s)(?=[\s,.:;]|$)" % RANGES)
STRING = re.compile(r'"((?:[^"]|"")*)"')
OPENS = {"(*OCAML": "OCAML*)", "(*OCAML-END": "OCAML-END*)"}


def ranges_of(s):
    return [(int(a), int(b or a)) for a, b in re.findall(r"(\d+)(?:\s*-\s*(\d+))?", s)]


def comments(s):
    """Where each comment of a Rocq text begins and ends, comments inside
    comments not counted; as tools/papp.py reads them (a string begins
    outside a comment only)."""
    out = []
    depth = 0
    i = 0
    in_str = False
    start = 0
    while i < len(s):
        if depth == 0 and s[i] == '"':
            in_str = not in_str
            i += 1
        elif in_str:
            i += 1
        elif s.startswith("(*", i):
            if depth == 0:
                start = i
            depth += 1
            i += 2
        elif depth and s.startswith("*)", i):
            depth -= 1
            i += 2
            if depth == 0:
                out.append((start, i))
        else:
            i += 1
    return out


class Mark(object):
    """A mark (* PORT-GAP(kind): words *) outside the sentences."""

    def __init__(self, kind, line, words, start, end):
        self.kind = kind
        self.line = line
        self.words = words
        self.start = start  # where the comment begins and ends
        self.end = end
        first = FIRST_LINES.match(words)
        self.lines = ranges_of(first.group(1)) if first else None  # the lines that it names first
        self.under = []  # the given texts under it


class Text(object):
    """A given text: a block, or the strings of a directive."""

    def __init__(self, pos, line, kind, name, strings, text):
        self.pos = pos
        self.line = line
        self.kind = kind  # block, block at the end, Constant, Inlined Constant, Inductive
        self.name = name
        self.strings = strings
        self.text = text
        self.note = None  # the lines that are named for it
        self.marks = []  # the marks over it
        self.modules = None
        self.holds = None  # the relation or the class, with its words
        self.why = None  # why nothing holds
        self.errors = []

    def shown(self):
        if self.kind.startswith("block"):
            return self.kind
        return "Extract %s %s" % (self.kind, self.name)


class Reading(object):
    """A ported file: its given texts, each with the note and the marks
    that stand over it; its marks; what could not be read."""

    def __init__(self, path, raw):
        self.path = path
        self.raw = raw
        self.errors = []  # (line, words)
        self.texts = []
        self.marks = []
        lines = raw.split("\n")
        # the blocks, as tools/assemble.sh reads them: whole lines
        blocks = []
        masked = list(raw)
        pos = 0
        on = None
        for n, l in enumerate(lines):
            if on is None and l in OPENS:
                on = (l, pos, n + 1, [])
            elif on is not None and l == OPENS[on[0]]:
                blocks.append((on[1], pos + len(l), on[2], on[0][2:], "\n".join(on[3])))
                for k in range(on[1], pos + len(l)):
                    if masked[k] != "\n":
                        masked[k] = " "
                on = None
            elif on is not None:
                if l in OPENS or l in OPENS.values():
                    self.errors.append((n + 1, "a line %s inside the block of line %d" % (l, on[2])))
                on[3].append(l)
            pos += len(l) + 1
        if on is not None:
            self.errors.append((on[2], "the block of OCaml that begins here does not end"))
        masked = "".join(masked)
        self.text = papp.blank(masked, False)
        self.spans = papp.sentences(self.text)
        events = []
        whole = set(comments(raw))
        for a, b, line, kind, body in blocks:
            # for Rocq the block is one comment, which begins and ends
            # where the block does, and stands outside every sentence
            if (a, b) not in whole or any(x < a < y for x, y in self.spans):
                self.errors.append((line, "the block of OCaml is not a comment of its own between two sentences"))
            name = "block" if kind == "OCAML" else "block at the end"
            events.append((a, "text", Text(a, line, name, "", [], body)))
        # the comments outside the sentences
        for start, end in comments(masked):
            if any(x < start < y for x, y in self.spans):
                continue
            c = masked[start:end]
            line = masked.count("\n", 0, start) + 1
            m = MARK.fullmatch(c)
            n = NOTE.fullmatch(c)
            if m:
                events.append((start, "mark", Mark(m.group(1), line, " ".join(m.group(2).split()), start, end)))
            elif n:
                events.append((start, "note", ranges_of(n.group(1))))
            else:
                events.append((start, "comment", None))
        for k, (a, b) in enumerate(self.spans):
            s = raw[a:b]
            line = raw.count("\n", 0, a) + 1
            if re.search(r"(?<![A-Za-z_0-9'.])Extract(?:ion)?(?![A-Za-z_0-9'])", self.text[a:b]):
                t = self.directive(a, line, s) if s.startswith("Extract") else None
                if t is None:
                    shown = " ".join(s.split())[:60]
                    self.errors.append((line, "a directive of the extraction that the tool does not read: %s" % shown))
                    events.append((a, "sentence", False))
                else:
                    events.append((a, "text", t))
                continue
            events.append((a, "sentence", self.bodiless(s, k)))
        events.sort(key=lambda e: e[0])
        # the note and the marks that stand over each text (THE GROUPS)
        note = None
        marks = []
        seen = False  # the group has a text
        beside = False  # only comments since the last note or mark
        for pos, what, x in events:
            if what == "note":
                note, marks, seen, beside = x, [], False, True
            elif what == "mark":
                self.marks.append(x)
                if beside:
                    marks = marks + [x]
                    note = x.lines or note
                else:
                    note, marks, seen = x.lines, [x], False
                beside = True
            elif what == "comment":
                if seen:
                    note, marks, seen, beside = None, [], False, False
            elif what == "sentence":
                beside = False
                if not x:
                    note, marks, seen = None, [], False
            else:
                x.note = note
                x.marks = list(marks)
                x.modules = papp.rocq_modules(self.text, self.spans, pos)
                for m in marks:
                    m.under.append(x)
                self.texts.append(x)
                seen = True
                beside = False

    def directive(self, pos, line, s):
        """The given text of a directive; None if it is not read."""
        strings = [x.replace('""', '"') for x in STRING.findall(s)]
        bare = " ".join(STRING.sub("S", s).split())
        m = re.fullmatch(r"Extract Constant (%s)((?: S)*) => S" % papp.PNAME, bare)
        if m:
            return Text(pos, line, "Constant", m.group(1), strings, None)
        m = re.fullmatch(r"Extract Inlined Constant (%s) => S" % papp.PNAME, bare)
        if m:
            return Text(pos, line, "Inlined Constant", m.group(1), strings, None)
        m = re.fullmatch(r"Extract Inductive (%s) => S \[((?: S)*) ?\]( S)?" % papp.PNAME, bare)
        if m:
            t = Text(pos, line, "Inductive", m.group(1), strings, None)
            t.eliminator = bool(m.group(3))
            return t
        return None

    def bodiless(self, s, k):
        """Whether the sentence may stand between a note or a mark and a
        given text: it has no body of ported code."""
        if re.match(
            r"(?:From|Require|Import|Arguments|Inductive|Record|Parameter|(?:Local\s+)?Open\s+Scope)"
            r"(?![A-Za-z_0-9'])",
            s,
        ):
            return True
        if papp.ABBREVIATION.fullmatch(s):
            return True
        m = re.match(r"Definition\s+(%s)(?![A-Za-z_0-9'.])" % papp.PNAME, s)
        if m and k + 1 < len(self.spans):
            a, b = self.spans[k + 1]
            nxt = " ".join(STRING.sub("S", self.raw[a:b]).split())
            if re.match(r"Extract (?:Inlined )?Constant %s(?![A-Za-z_0-9'.])" % re.escape(m.group(1)), nxt):
                return True
        return False


# ---- R3: the form of a type ----------------------------------------------

OPEN = ("(", "[", "{")
CLOSE = (")", "]", "}")
ITEM = ("type", "and", "let", "module", "exception", "val", "end", "include", "open", "external")


def split_top(toks, sep):
    """The tokens cut at each [sep] that stands outside brackets."""
    out = [[]]
    depth = 0
    for t in toks:
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
        if depth == 0 and t == sep:
            out.append([])
        else:
            out[-1].append(t)
    return out


def fields_of(toks):
    """The names of the fields of [f : T; mutable g : U] (what stands
    between the braces of a record); None if it is not read."""
    out = []
    for part in split_top(toks, ";"):
        if not part:
            continue
        if part[0] == "mutable":
            part = part[1:]
        if len(part) < 3 or part[1] != ":" or not IDENT.fullmatch(part[0]):
            return None
        out.append(part[0])
    return out or None


def shape_of(toks):
    """What the definition of a type is, from the tokens after its [=]:
    ("variant", [(constructor, number of arguments, fields or None)]) or
    ("record", fields); None if it is not read (a type that is equal to
    another, a function, a tuple, polymorphic variants)."""
    toks = list(toks)
    if not toks:
        return None
    if toks[0] == "{" and toks[-1] == "}":
        fs = fields_of(toks[1:-1])
        return ("record", fs) if fs else None
    if toks[0] == "|":
        toks = toks[1:]
    ctors = []
    for part in split_top(toks, "|"):
        if not part:
            return None
        name = part[0]
        if not (IDENT.fullmatch(name) and name[0].isupper()):
            return None
        if len(part) == 1:
            ctors.append((name, 0, None))
        elif part[1] == "of" and len(part) > 2:
            args = part[2:]
            if args[0] == "{" and args[-1] == "}":
                fs = fields_of(args[1:-1])
                if fs is None:
                    return None
                ctors.append((name, len(fs), fs))
            else:
                ctors.append((name, len(split_top(args, "*")), None))
        else:
            return None
    return ("variant", ctors) if ctors else None


def definitions_in(toks):
    """(name, the tokens of the definition) for each [type .. T = ..] and
    [and .. T = ..] of a text; a type of a module M of the text is M.T."""
    out = []
    path = []
    opened = []  # for each [struct] or [sig] that is open: the module, or None
    i = 0
    while i < len(toks):
        t = toks[i]
        if t == "module" and i + 1 < len(toks) and toks[i + 1][:1].isupper():
            pending = toks[i + 1]
            j = i + 2
            while j < len(toks) and toks[j] not in ("struct", "sig") and toks[j] not in ITEM:
                j += 1
            if j < len(toks) and toks[j] in ("struct", "sig"):
                # [module M = struct], [module M : sig]: what follows is of M
                opened.append(pending)
                path.append(pending)
                i = j + 1
                continue
        elif t in ("struct", "sig", "object", "begin"):
            opened.append(None)
        elif t == "end":
            if opened and opened.pop() is not None:
                path.pop()
        elif t in ("type", "and"):
            j = i + 1
            while j < len(toks) and toks[j] != "=" and j < i + 12 and toks[j] not in ITEM:
                j += 1
            if j < len(toks) and toks[j] == "=" and IDENT.fullmatch(toks[j - 1]) and toks[j - 1][0].islower():
                depth = 0
                k = j + 1
                while k < len(toks):
                    u = toks[k]
                    if u in OPEN:
                        depth += 1
                    elif u in CLOSE:
                        depth -= 1
                        if depth < 0:
                            break
                    elif depth == 0 and u in ITEM:
                        break
                    k += 1
                out.append((".".join(path + [toks[j - 1]]), toks[j + 1:k]))
                i = j + 1
                continue
        i += 1
    return out


def xs(n):
    return ["x__%d" % (i + 1) for i in range(n)]


def pattern(name, n, fields):
    v = xs(n)
    if fields is not None:
        return "%s { %s }" % (name, "; ".join("%s = %s" % (f, x) for f, x in zip(fields, v)))
    if n == 0:
        return name
    if n == 1:
        return "%s %s" % (name, v[0])
    return "%s (%s)" % (name, ", ".join(v))


def record(fields):
    return "{ %s }" % "; ".join("%s = %s" % (f, x) for f, x in zip(fields, xs(len(fields))))


def args(n):
    return "x__1" if n == 1 else "(%s)" % ", ".join(xs(n))


ANY_TYPE = "any__type"  # one token


def typed(s, tname, with_type):
    return "(%s : %s)" % (s, tname) if with_type else s


def is_with_any_type(toks, form):
    """Whether the tokens are the form, where the form has ANY_TYPE for
    the type of an annotation [(E : T)]: there the tokens have a type, as
    words (names, dots, type variables, [_], brackets and commas, up to
    the bracket that closes the annotation)."""
    i = 0
    for f in form:
        if f == ANY_TYPE:
            depth = 0
            k = i
            while k < len(toks) and not (depth == 0 and toks[k] == ")"):
                if toks[k] == "(":
                    depth += 1
                elif toks[k] == ")":
                    depth -= 1
                elif not (toks[k] in (".", ",") or IDENT.fullmatch(toks[k].lstrip("'"))):
                    return False
                k += 1
            if k == i:
                return False
            i = k
        elif i < len(toks) and toks[i] == f:
            i += 1
        else:
            return False
    return i == len(toks)


def is_form(s, make):
    """Whether the string is a form: (yes, by D4). [make with_type tname]
    gives the forms; D4 is the form without the annotation of the type, or
    with another type in the annotation."""
    toks = words(s)
    if any(toks == words(f) for f in make(True, None)):
        return True, False
    if any(toks == words(f) for f in make(False, None)):
        return True, True
    return any(is_with_any_type(toks, words(f)) for f in make(True, ANY_TYPE)), True


def strings_of(shape, tname, with_type, written=None):
    """The form of a type: for each constructor the strings that may stand
    for it, and the eliminator. With the annotation of the type, as
    tools/declgen/emit_types.ml writes the form, or without it (D4);
    [written] is what stands for the type in an annotation, if not its
    name."""
    kind, what = shape
    path = tname.split(".")[:-1]
    tname = written or tname
    if kind == "variant":
        what = [(".".join(path + [name]), n, fields) for name, n, fields in what]
        ctors = []
        for name, n, fields in what:
            body = typed(pattern(name, n, fields), tname, with_type)
            function = body if n == 0 else "(fun %s -> %s)" % (args(n), body)
            # a constructor without an inline record is its name, or, when
            # a later type hides it, the same function with the type
            ctors.append([function] if fields is not None else [name, function])
        match = "(fun %s x__0 -> match %s with %s)" % (
            " ".join("f__%d" % (i + 1) for i in range(len(what))),
            typed("x__0", tname, with_type),
            " | ".join(
                "%s -> f__%d %s" % (pattern(name, n, fields), i + 1, "()" if n == 0 else " ".join(xs(n)))
                for i, (name, n, fields) in enumerate(what)
            ),
        )
        return ctors, match
    n = len(what)
    maker = "(fun %s -> %s)" % (args(n), typed(record(what), tname, with_type))
    match = "(fun f__1 x__0 -> let %s = x__0 in f__1 %s)" % (typed(record(what), tname, with_type), " ".join(xs(n)))
    return [[maker]], match


def rocq_arities(sentence, name):
    """The numbers of arguments of the constructors of the Rocq type
    [name] in an [Inductive] sentence, or the number of fields of a
    [Record]; None if it is not read. As words."""
    s = papp.blank(sentence, False)
    toks = re.findall(r":=|->|[A-Za-z_][A-Za-z_0-9'.]*|\S", s)
    if toks[:1] == ["Record"]:
        if len(toks) < 2 or toks[1] != name or "{" not in toks or toks[-1] != "}":
            return None
        inside = toks[toks.index("{") + 1:-1]
        parts = [p for p in split_top(inside, ";") if p]
        return [len(parts)] if all(len(p) > 2 and p[1] == ":" for p in parts) else None
    if toks[:1] != ["Inductive"]:
        return None
    for decl in split_top(toks[1:], "with"):
        if not decl or decl[0] != name or ":=" not in decl:
            continue
        body = decl[decl.index(":=") + 1:]
        if body[:1] == ["|"]:
            body = body[1:]
        out = []
        for c in split_top(body, "|"):
            if not c or not re.fullmatch(papp.PNAME, c[0]):
                return None
            n = 0
            i = 1
            # binders (a b : T), then perhaps [: T1 -> .. -> R]
            while i < len(c) and c[i] == "(":
                depth = 0
                j = i
                while j < len(c):
                    if c[j] == "(":
                        depth += 1
                    elif c[j] == ")":
                        depth -= 1
                        if depth == 0:
                            break
                    j += 1
                group = c[i + 1:j]
                if ":" not in group:
                    return None
                n += group.index(":")
                i = j + 1
            if i < len(c):
                if c[i] != ":":
                    return None
                n += len(split_top(c[i + 1:], "->")) - 1
            out.append(n)
        return out
    return None


# ---- the relations --------------------------------------------------------


def r1(donor, toks, note):
    """R1 for the tokens of a text: (holds, words, an error or None)."""
    if not toks:
        return False, "the text has no token", None
    if note and donor.at(note) == toks:
        return True, "the donor's lines %s" % show(note), None
    found = donor.find(toks)
    if found and note:
        return False, None, "the note names the lines %s, and the text is the donor's lines %s" % (
            show(note),
            show(found[:3]),
        )
    if found:
        return (
            False,
            None,
            "no note of lines stands over it, and the text is the donor's lines %s: write (* %s *) before it"
            % (show(found[:3]), show(found[:1])),
        )
    return False, "it is not the donor's text%s" % (" of the lines %s" % show(note) if note else ""), None


def check_block(rd, donor, t):
    ok, w, err = r1(donor, words(t.text), t.note)
    if ok:
        t.holds = "R1: " + w
    elif err:
        t.errors.append(err)
        t.why = "its lines are not named rightly"
    else:
        t.why = w


def check_constant(rd, donor, t):
    """An Extract Constant: Rocq prints [type PARAMS NAME = TEXT] or [let
    NAME = TEXT]."""
    params = t.strings[:-1]
    head = []
    if len(params) == 1:
        head = words(params[0])
    elif len(params) > 1:
        head = ["("] + sum(([","] + words(p) for p in params), [])[1:] + [")"]
    text = words(t.strings[-1])
    lines = donor.at(t.note) if t.note else []
    for name, d5 in ((t.name, ""), (t.name.rstrip("_"), ", D5 (the name has _ at its end)")):
        if d5 and name == t.name:
            continue
        printed = head + [name, "="] + text
        for kw in ("type", "let"):
            if lines == [kw] + printed:
                t.holds = "R1, D1%s: [%s %s = ..] of the donor's lines %s" % (d5, kw, name, show(t.note))
                t.defines = name if kw == "type" else None
                return
        found = donor.find(printed)
        if found:
            if t.note:
                t.errors.append(
                    "the note names the lines %s, and [%s = ..] is the donor's text at %s"
                    % (show(t.note), name, show(found[:3]))
                )
            else:
                t.errors.append(
                    "no note of lines stands over it, and [%s = ..] is the donor's text at %s: write the note before it"
                    % (name, show(found[:3]))
                )
            t.why = "its lines are not named rightly"
            return
    if text[:2] == ["(", ")"] and len(text) > 2 and text[2] in ("include", "module"):
        ok, w, err = r1(donor, text[2:], t.note)
        if ok:
            t.holds = "R1, D2 (an item after [()]): " + w
        elif err:
            t.errors.append(err)
            t.why = "its lines are not named rightly"
        else:
            t.why = w
        return
    t.why = "what Rocq prints, [%s = ..], is not the donor's text%s" % (
        t.name,
        " of the lines %s" % show(t.note) if t.note else "",
    )


def own_name(name, text):
    """Whether the text is the name: (yes, the words of D5 or "")."""
    s = " ".join(text.split())
    if s == name:
        return True, ""
    if not re.fullmatch(papp.PPATH, s):
        return False, ""
    if name.rstrip("_") == s and name != s:
        return True, ", D5 (the name has _ at its end)"
    if name.rstrip("_") == s.replace(".", "_"):
        return True, ", D5 (the name has _ for the dots of the path)"
    return False, ""


def check_setter(rd, donor, t):
    s = " ".join(t.strings[0].split())
    m = re.fullmatch(r"\(fun t((?: [a-z_][A-Za-z_0-9']*)+) -> \{ t with (.*) \}\)", s)
    items = [re.fullmatch(r" ?(%s) = (%s) ?" % (papp.PPATH, papp.PNAME), x) for x in m.group(2).split(";")] if m else []
    params = m.group(1).split() if m else []
    in_order = m and all(items) and [i.group(2) for i in items] == params
    if not in_order or "t" in params or len(set(params)) != len(params):
        t.why = "the text is not (fun t p1 .. -> { t with F1 = p1; .. }), one field for each parameter, in order"
        return
    fields = tuple(i.group(1).split(".")[-1] for i in items)
    if donor.no_updates:
        t.why = "the record updates of the donor are not known (decl/UPDATES.tsv: %s)" % donor.no_updates
        return
    if not t.note:
        t.why = "no lines are named: the places of the record update in the donor"
        return
    problems = []
    places = set()
    first_only = 0
    named = []
    for a, b in t.note:
        here = [u for u in donor.updates if u.first == a]
        good = [u for u in here if u.given == fields]
        if not here:
            problems.append("no record update begins at line %d of the donor" % a)
        elif not good:
            problems.append("the record update of line %d gives the fields %s" % (a, " ".join(here[0].given)))
        else:
            u = good[0]
            named.append(u)
            places.add(u.place)
            if b != a and u.last != b:
                problems.append("the record update of line %d ends at line %d, not %d" % (a, u.last, b))
            elif b == a and u.last != a:
                first_only += 1
    if len(places) > 1:
        problems.append("the places named are updates of %d record types" % len(places))
    if not problems:
        # every update of the same fields of the same type is named
        more = [u for u in donor.updates if u.given == fields and u.place in places and u not in named]
        if more:
            problems.append(
                "the donor has the same record update at %s too: the note names every place"
                % ", ".join(str(u.first) for u in more)
            )
        # the record of the Rocq definition is of the donor's type
        rocq = rocq_fields(rd, t)
        if rocq is None:
            problems.append(
                "the sentence before the directive is not [Definition %s .. := {| F := .. ; .. |}]" % t.name
            )
        elif rocq != list(named[0].all):
            problems.append(
                "the record of the Rocq definition has the fields %s, the type of the donor %s"
                % (" ".join(rocq), " ".join(named[0].all))
            )
    if problems:
        t.errors.extend(problems)
        t.why = "the places of the record update are not named rightly"
        return
    t.holds = "R2%s: a record update of the fields %s begins at each of the donor's lines %s, and nowhere else" % (
        ", D3 (%d of the places named by the line where the update begins)" % first_only if first_only else "",
        " ".join(fields),
        show(t.note),
    )


SETTER = re.compile(r"Definition\s+(%s)(?![A-Za-z_0-9'.])[^{}]*:=\s*\{\|(.*)\|\}\s*" % papp.PNAME, re.S)


def rocq_fields(rd, t):
    """The fields of the record of the Rocq definition of a setter, in
    order: the sentence before the directive is [Definition NAME .. := {|
    F := .. ; .. |}]. A [_] at the end of a Rocq field is left out, and so
    are the modules before it. None if the sentence is not that."""
    before = [sp for sp in rd.spans if sp[0] < t.pos]
    m = SETTER.fullmatch(rd.text[before[-1][0]:before[-1][1]]) if before else None
    if not m or m.group(1) != t.name:
        return None
    out = []
    for f in m.group(2).split(";"):
        g = re.fullmatch(r"\s*(%s)\s*:=.*" % papp.PPATH, f, re.S)
        if not g:
            return None
        out.append(g.group(1).split(".")[-1].rstrip("_"))
    return out


def definition_of(rd, t, tname):
    """The OCaml definition of the type [tname] that the file gives: (the
    tokens, None) or (None, why not). It is taken from a text that holds
    R1."""
    last = tname.split(".")[-1]
    if t.modules is None:
        return None, (
            "the directive stands in a functor or a module type, or the words do not say in which module: "
            "the tool does not say which definition of %s it means" % tname
        )
    held = []
    for y in rd.texts:
        if y.kind == "Constant" and getattr(y, "defines", None):
            # a directive gives a type to the module in which it stands
            if y.modules == t.modules and "." not in tname:
                toks = ["type", y.defines, "="] + words(y.strings[-1])
                held += [(d, y) for name, d in definitions_in(toks) if name == tname]
        elif y.kind.startswith("block") and y.holds and (not t.modules or "." in tname):
            held += [(d, y) for name, d in definitions_in(words(y.text)) if name == tname]
    if len(held) == 1:
        return held[0][0], None
    if held:
        return None, "the file gives %d OCaml definitions of %s (the texts of lines %s)" % (
            len(held), tname, ", ".join(str(y.line) for _, y in held))
    # is it given by a text that does not hold R1?
    for y in rd.texts:
        toks = None
        if y.kind == "Constant":
            toks = ["type", y.name.rstrip("_"), "="] + words(y.strings[-1])
        elif y.kind.startswith("block"):
            toks = words(y.text)
        if toks and not y.holds and any(name in (tname, last) for name, _ in definitions_in(toks)):
            return None, "the definition of %s is in the text of line %d, which does not hold R1" % (tname, y.line)
    return None, "the file gives no OCaml definition of %s that holds R1" % tname


def check_inductive(rd, donor, t):
    tname = " ".join(t.strings[0].split())
    if not re.fullmatch(papp.PPATH, tname):
        t.why = (
            "the type is written out in the directive (a polymorphic variant, a tuple with labels): "
            "that text is the definition, and it is no line of the donor"
        )
        return
    toks, why = definition_of(rd, t, tname)
    if toks is None:
        t.why = why
        return
    shape = shape_of(toks)
    if shape is None:
        t.why = "the OCaml definition of %s is not read" % tname
        return
    ctors, match = strings_of(shape, tname, True)
    given = t.strings[1:]
    k = len(ctors)
    eliminator = getattr(t, "eliminator", False)
    if len(given) != k + (1 if eliminator else 0):
        t.why = "the definition of %s has %d constructors, the directive %d strings for them" % (
            tname,
            k,
            len(given) - (1 if eliminator else 0),
        )
        return
    d4 = False
    functions = False
    for n, (s, cands) in enumerate(zip(given, ctors)):
        ok, ann = is_form(s, lambda with_type, written: strings_of(shape, tname, with_type, written)[0][n])
        if not ok:
            t.why = "the string of the constructor %d is not the form: the form is %s" % (n + 1, cands[-1])
            return
        d4 = d4 or ann
        functions = functions or words(s)[:2] == ["(", "fun"]
    if eliminator:
        ok, ann = is_form(given[k], lambda with_type, written: [strings_of(shape, tname, with_type, written)[1]])
        if not ok:
            t.why = "the eliminator is not the form: the form is %s" % match
            return
        d4 = d4 or ann
    elif functions:
        t.why = "a constructor is a function and the directive has no eliminator"
        return
    # the Rocq type: as many constructors, each with as many arguments
    wanted = [len(shape[1])] if shape[0] != "variant" else [n for _, n, _ in shape[1]]
    rocq = None
    for a, b in reversed([sp for sp in rd.spans if sp[0] < t.pos]):
        rocq = rocq_arities(rd.raw[a:b], t.name)
        if rocq is not None:
            if papp.rocq_modules(rd.text, rd.spans, a) != t.modules:
                rocq = None
            break
    if rocq is None:
        t.why = (
            "the Rocq type %s is not read (the nearest Inductive or Record of that name before the "
            "directive, in the same module)" % t.name
        )
        return
    if rocq != wanted:
        t.why = "the Rocq type %s has constructors of %s arguments, the OCaml definition of %s" % (t.name, rocq, wanted)
        return
    t.holds = "R3%s: the form of the %s %s, whose definition the file gives" % (
        ", D4 (the type of an annotation is not compared)" if d4 else "",
        shape[0],
        tname,
    )


def together(line, toks):
    """Whether the tokens stand together among the tokens of the lines."""
    return any(line[i:i + len(toks)] == toks for i in range(len(line) - len(toks) + 1))


def record_of(rd, t, name):
    """The fields of the record [name], from the definition that the file
    gives for the place of the text t: (fields, None) or (None, why not)."""
    toks, why = definition_of(rd, t, name)
    if toks is None:
        return None, why
    shape = shape_of(toks)
    if not shape or shape[0] != "record":
        return None, "the OCaml definition of %s is no record" % name
    return shape[1], None


def records_of(rd):
    """The names of the types that the texts of the file define."""
    out = []
    for y in rd.texts:
        toks = None
        if y.kind == "Constant" and getattr(y, "defines", None):
            toks = ["type", y.defines, "="] + words(y.strings[-1])
        elif y.kind.startswith("block") and y.holds:
            toks = words(y.text)
        for name, _ in definitions_in(toks or []):
            if name not in out:
                out.append(name)
    return out


def check_inlined(rd, donor, t):
    """An Extract Inlined Constant that is no setter."""
    # the classes and the forms have no string of OCaml: they are read
    # with single white space. The tokens are cut from the text as it
    # stands: white space inside a string of the text is kept.
    s = " ".join(t.strings[0].split())
    toks = words(t.strings[0])
    ok, d5 = own_name(t.name, s)
    if ok:
        t.holds = "its own name%s" % d5
        return
    m = re.fullmatch(r"\(\(fun \(\) -> (\w+)\), \(function (\w+) -> Some \(\) \| _ -> None\)\)", s)
    if m and m.group(1) == m.group(2) == t.name:
        t.holds = "the pair of an exception"
        return
    if NUMBER.fullmatch(s[2:-1] if s.startswith("(-") and s.endswith(")") else s):
        d = re.search(
            r"(?<![A-Za-z_0-9'.])Definition\s+%s\s*:[^:=]*:=\s*\(?(-?\d+)\)?(?:%%[A-Za-z_]+)?\s*\.(?=\s)"
            % re.escape(t.name),
            rd.text,
        )
        if d:
            try:
                value = int(s.strip("()").rstrip("lLn").replace("_", ""), 0)
            except ValueError:
                value = None
            if value != int(d.group(1)):
                t.why = "the number %s is not the %s of the Rocq definition" % (s, d.group(1))
                return
            t.holds = "a number, that of the Rocq definition"
        elif t.note and all(together(donor.at([r]), toks) for r in t.note):
            t.holds = "a number, a literal of each of the donor's lines %s" % show(t.note)
        else:
            t.why = (
                "the Rocq constant %s is a parameter, and the number is no literal of the donor's lines%s"
                % (t.name, " %s" % show(t.note) if t.note else ": no lines are named")
            )
        return
    # the reader of a field, the maker and the eliminator of a record
    m = re.fullmatch(r"\(fun \(x__0 : (?:_ |\(_(?:, _)*\) )?(%s)\) -> x__0\.(\w+)\)" % papp.PPATH, s)
    if m:
        fields, why = record_of(rd, t, m.group(1))
        if fields is None:
            t.why = why
        elif m.group(2) not in fields:
            t.why = "%s is no field of %s" % (m.group(2), m.group(1))
        elif t.name.rstrip("_") != m.group(2):
            t.why = "the constant %s reads the field %s" % (t.name, m.group(2))
        else:
            t.holds = "R3: the reader of the field %s of the record %s" % (m.group(2), m.group(1))
        return
    if toks[:3] == ["(", "fun", "x__1"] or toks[:4] == ["(", "fun", "x__0", "f__1"]:
        for name in records_of(rd):
            fields, _ = record_of(rd, t, name)
            if fields is None:
                continue
            v = " ".join(xs(len(fields)))
            forms = (
                ("maker", "(fun %s -> %%s)" % v),
                ("eliminator", "(fun x__0 f__1 -> let %%s = x__0 in f__1 %s)" % v),
            )
            for what, form in forms:
                ok, ann = is_form(
                    s, lambda with_type, written: [form % typed(record(fields), written or name, with_type)]
                )
                if ok:
                    t.holds = "R3%s: the %s of the record %s" % (
                        ", D4 (the type of an annotation is not compared)" if ann else "",
                        what,
                        name,
                    )
                    return
        t.why = "it is not the maker or the eliminator of a record whose OCaml definition the file gives"
        return
    # an expression that is all that the donor has on each line named
    if t.note and all(donor.at([r]) == toks for r in t.note):
        t.holds = "R1: each of the donor's lines %s" % show(t.note)
        return
    t.why = (
        "it is no name of its own, no pair of an exception, no number, no form of a record, "
        "and not the donor's lines"
    )


def check(path, raw=None):
    """The reading of a ported file, with the verdict of each given text
    and the errors."""
    raw = open(path).read() if raw is None else raw
    rd = Reading(path, raw)
    donor = donor_of(path)
    rd.donor = donor
    if donor.why:
        rd.errors.append((1, donor.why))
    # the blocks and the directives of types and values first: R3 leans
    # on the definitions that hold R1
    for t in rd.texts:
        if t.kind.startswith("block"):
            check_block(rd, donor, t)
        elif t.kind == "Constant":
            check_constant(rd, donor, t)
    for t in rd.texts:
        if t.kind == "Inductive":
            check_inductive(rd, donor, t)
        elif t.kind == "Inlined Constant":
            if t.name.startswith("update_"):
                check_setter(rd, donor, t)
            else:
                check_inlined(rd, donor, t)
    for t in rd.texts:
        if donor.why and t.holds and t.holds.startswith(("R1", "R2", "R3")):
            t.holds = None
            t.why = "the donor is not read"
        over = [m for m in t.marks if m.kind in OVER]
        for e in t.errors:
            rd.errors.append((t.line, "%s: %s" % (t.shown(), e)))
        if not t.holds and not over and not t.errors:
            rd.errors.append(
                (t.line, "%s is OCaml text that nothing checks and no mark stands over: %s" % (t.shown(), t.why))
            )
    for m in rd.marks:
        if m.kind in JUDGED and m.under and all(t.holds for t in m.under):
            m.needless = True
            rd.errors.append(
                (m.line, "the mark PORT-GAP(%s) is not needed: %s under it (write the lines as a note: (* N-M *))"
                 % (m.kind, "the text holds" if len(m.under) == 1 else "each of the %d texts holds" % len(m.under)))
            )
    return rd


def main(files):
    count = collections.Counter()
    marks = collections.Counter()
    errors = 0
    listing = os.environ.get("GIVEN_ALL")
    for path in files:
        rd = check(path)
        for t in rd.texts:
            over = [m for m in t.marks if m.kind in OVER]
            if t.holds:
                count[t.holds.split(":")[0].split(",")[0].split(" (")[0]] += 1
            elif over:
                count["under a mark"] += 1
                for m in over:
                    marks[m] += 1
            else:
                count["nothing"] += 1
            if listing:
                where = "; under the mark%s %s" % (
                    "s" if len(over) > 1 else "",
                    ", ".join("PORT-GAP(%s) of line %d" % (m.kind, m.line) for m in over),
                ) if over else ""
                print("%s:%d\t%s\t%s%s" % (path, t.line, t.shown(), t.holds or "NOTHING HOLDS: %s" % t.why, where))
        for line, w in sorted(rd.errors):
            print("%s:%d: %s" % (path, line, w))
            errors += 1
    kinds = collections.Counter(m.kind for m in marks)
    print(
        "given: %d texts of OCaml in %d files: %d are the donor's lines (R1), %d setters of record updates "
        "(R2), %d forms of types (R3), %d of a named class (%d names, %d pairs of exceptions, %d numbers), "
        "%d that nothing checks under %d marks (%s); %s"
        % (
            sum(count.values()),
            len(files),
            count["R1"],
            count["R2"],
            count["R3"],
            count["its own name"] + count["the pair of an exception"] + count["a number"],
            count["its own name"],
            count["the pair of an exception"],
            count["a number"],
            count["under a mark"],
            len(marks),
            ", ".join("%d %s" % (kinds[k], k) for k in OVER if kinds[k]) or "none",
            "%d wrong" % errors if errors else "nothing wrong",
        )
    )
    return 1 if errors else 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: given.py FILE.v ...")
    sys.exit(main(sys.argv[1:]))
