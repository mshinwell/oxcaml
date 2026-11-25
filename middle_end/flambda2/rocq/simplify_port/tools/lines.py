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


"""lines.py : the notes of lines before the definitions of the ported files,
against the lines of the compiler's own definitions (GUIDE.md, section 1).
It follows no file of the compiler.

    lines.py FILE.v ...      (the Makefile's target lines, a part of check)

DIR/Foo.v follows middle_end/flambda2/simplify/DIR/foo.ml, its DONOR,
definition by definition, and says before each definition which lines of
the donor it follows: a NOTE OF LINES, (* 12-20 *). tools/given.py says
how a note is written and which note stands over a sentence (THE GROUPS),
and compares the OCaml TEXT that a file gives with the donor's lines. This
tool compares the NOTE OF A DEFINITION with the lines where the donor
defines the thing of that name. decl/DONOR-ITEMS.tsv has those lines from
the typed tree of the donor (tools/declgen/donors.ml): for each thing that
the donor defines, at any depth of modules, its kind, the modules around
it, its name, the first and the last line of its definition, and the first
and the last line of the whole item (for [let rec f .. and g ..] and for
[type a = .. and b = ..] the item is all of them together).

A DEFINITION is a sentence of the ported file that begins with [Definition
NAME], [Fixpoint NAME], [Inductive NAME], [Record NAME], [Module NAME] or
[Module Type NAME]. ITS ITEMS are the rows of the table for the donor that
have
- its kind: a value for a Fixpoint; a value or a type for a Definition; a
  type for an Inductive or a Record; a module; a module type;
- its name, a [_] at the end of either name left out (Rocq wants [t_]
  where the compiler has [t]);
- its modules: the modules of Rocq that are open where the sentence
  begins ([Module M.] .. [End M.], as tools/papp.py reads them) are the
  modules around the item, name for name (a functor of the donor counts
  as a module of its name).

THE RULE.
- A definition that has an item MUST HAVE A NOTE: the lines of its group,
  as tools/given.py reads the groups. They are the lines of the note that
  began the group; or, if a mark began it, the lines that the mark names
  first. (A mark that JOINS a group may name other lines, those of what
  the mark is about: for this tool they do not take the place of the
  note's.) So a note counts for every definition of its group (an
  [Inductive t_] and the [Definition t] after it); a definition whose
  group has none is an error.
- THE NOTE IS ONE RANGE, and the tokens that begin on its lines are the
  tokens of the lines of ONE of the items: of its own definition, or of
  the whole item that defines it together with others. Tokens are
  compared, as tools/given.py reads them: blank lines and lines of comment
  at either end of the range are free. Anything else is an error, and the
  tool says the lines of the items. A note that names only the FIRST
  lines of the definition is wrong; so are two ranges.
- [Module X := ..] (the abbreviation of a module, the application of a
  functor: one sentence) is judged in RUNS. A run is the sentences of
  that form that follow one another with nothing between them: a comment
  between two of them ends the run, and so does any other sentence.
  EVERY MEMBER of a run is found by its name in the table, as one item
  (a sentence of that form with no item is not judged and ends the run;
  one with two items is an error). The note before the first member is
  one range, and its tokens are the tokens of the lines of the members'
  items, one after the other, in the order of the members. So the note
  goes from the first line of the first member's item to the last line
  of the last member's, and between two members the donor has NOTHING
  ELSE: blank lines and comments only. A run of one is the rule above.
- A CLAUSE [with NAME ..] of a Fixpoint defines NAME, as the donor's
  [and NAME ..] does. The tool takes for a clause a line of the Fixpoint
  that begins AT THE MARGIN of the Fixpoint (the column of the word
  [Fixpoint]) with [with NAME] and then [(], [{] or [:]. ITS ITEM is the
  donor's value NAME in the modules of the Fixpoint (a [_] at the end of
  either name left out, as for a definition); if the note of the
  Fixpoint is right, it is one that the donor defines TOGETHER with the
  Fixpoint's item (in one [let rec .. and ..]). ITS NOTE is, of the
  comments that stand directly before the clause (only blanks between
  them and the clause; a mark or another comment may stand among them),
  the last one that is a note of lines. The note is ONE RANGE, and its
  tokens are the tokens of the lines of the item's OWN definition (the
  lines of [and NAME ..]): the lines of the whole item are wrong here,
  and a clause that has an item and no note is an error. THE TOOL FAILS
  CLOSED: each of these is an error, and nothing more is judged of the
  line. A line at the margin of the Fixpoint that begins with [with] and
  is not of that shape. A line that begins at another column with [with
  NAME] and then [(], [{] or [:]: a clause is written at the margin (the
  [with] of a [match] does not look so). A clause for which more than
  one item is left (the donor defines NAME twice there). A clause whose
  item the donor does not define together with the Fixpoint's.
- A NOTE INSIDE a Definition or a Fixpoint whose own note is right names
  lines inside the whole item of the donor. So does a comment inside it
  that begins with lines and then a colon, a semicolon or a comma
  ([12-13: words]). That is ALL that is checked of them. The note of a
  clause is no note inside.

NOT JUDGED, and counted in the line of numbers:
- GIVEN: a [Definition NAME] that the directive [Extract Constant NAME] or
  [Extract Inlined Constant NAME] follows. Its OCaml text is given, and
  make given compares that text with the lines of its note (the note of
  a setter names places, not the lines of an item);
- NO ITEM: the donor has nothing of that kind under that name in those
  modules. A function that the port adds (a helper, a local function of
  the donor that has a name here), a type that the donor does not name,
  a module that the donor makes by applying a functor and the port
  writes out;
- IN A FUNCTOR OR A MODULE TYPE of the ported file: the words do not say
  which module of the donor that is. These definitions are LISTED AND NOT
  CHECKED: their notes are compared with nothing;
- A CLAUSE [with NAME ..] whose name the donor has under no value in
  those modules, or whose Fixpoint is in a functor or a module type of
  the file: counted with the clauses, apart from the definitions;
- every other sentence ([Parameter], a directive, [End]): no definition
  for this tool.
With LINES_ALL in the environment the tool first prints one line for each
definition and for each clause: its note, and its class or what is wrong.

The tool prints the errors and then one line of numbers; its exit status
is 1 if there is an error. If the donor is not read (tools/given.py: the
checksum of decl/DONOR-TOKENS.tsv; decl/DONOR-ITEMS.tsv is not there, has
rows of another width, or has not read the donor), that is an error, and
no definition of the file is judged.

WHAT THE TOOL DOES NOT ESTABLISH.
- That the Rocq definition IS a port of those lines. Only the note is
  compared, with the lines where the donor defines a thing of the same
  name, kind and modules. The body of the definition is not read.
- Anything about the definitions that are not judged: those in a functor
  or a module type of the file, and those that the donor has under no
  such name. The line of numbers says how many they are. Their notes
  are compared with nothing. They were read once by hand, after this
  tool was written (two of them, in a functor, had been found wrong
  when that work was reviewed, and mended): each note against all the
  lines of the donor that it names. No number was found wrong. Two
  notes named a whole functor where the definition follows the
  signature of the functor's argument; they name those lines now. 24
  definitions that the donor has at lines of their own had no note,
  and have one. The 41 remain without a note of their own for these
  reasons: what the donor makes by [include] or by applying a functor
  and the file writes out has no lines of its own in the donor (the
  note or the mark before the first of them, or before their module,
  names that line); a member of a run of [Module X := ..] has its
  line in the donor and is under the note of its run; what the file
  adds of its own, and a type that the donor does not name, have no
  lines in the donor. Nothing repeats that reading.
- WHICH OF TWO ITEMS of one name a definition follows. The donor may
  define a name twice in one module (the later hiding the earlier), and
  it may have a type and a value of one name, either of which a
  [Definition] can be. The note must be the lines of one of them: the
  tool cannot tell which of the two is meant, so the note of the other
  one passes.
- That a NOTE INSIDE a definition names the right lines. It is checked
  only to lie inside the lines of its item, and only in a definition
  that the tool judges: these are the notes that the line of numbers
  counts. Whether such a note begins and ends where a part of the item
  does (GUIDE.md, section 1, has the form of such a note) is checked by
  NO TOOL. When this tool was written, each of the notes that the line
  counts was read once by hand against the donor: the line of Rocq
  after the note against the donor's lines at the two ends of its range
  and just outside them. The notes that scans of the layout of the
  donor's text doubted (the scans are not kept in the tree) were read
  in full. A note inside a definition that is NOT judged is compared
  with nothing and is not counted; there were nine (four in
  Simplify_binary_primitive.v, five in Simplify_switch_expr.v), and
  they were read when that work was reviewed, and again with the notes
  before the definitions that are not judged. Nothing repeats these
  readings.
- Of a CLAUSE [with NAME ..]: that its body is a port of those lines,
  as for a definition. A clause whose line does not begin with [with]
  (one that follows the end of another function on one line) is not
  found, and no error is said. A note inside the body of a clause is
  checked to lie inside the whole item of the Fixpoint, not inside the
  lines of the clause. The [with NAME] of an [Inductive] (types that
  are defined together) is not read: the note of the Inductive is all
  that is judged of them.
- The lines that a mark names ([PORT-GAP(sort): 12-13, words]), but for
  the mark that begins a group: they are compared with nothing. What
  was read once by hand, when this tool was written: the lines that
  each mark names FIRST (199 marks name lines), and 85 further numbers
  of lines in the words of marks and notes, which a search of the text
  found. A number of a line that the search did not find was not read.
- The notes that stand before no definition (before a block of OCaml or a
  directive: make given), or inside a sentence that is no Definition and
  no Fixpoint.
- It is no parser of Rocq: the sentences, the modules and the groups are
  read as tools/papp.py and tools/given.py read them, as words.
"""
import collections
import os
import re
import sys

TOOLS = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, TOOLS)
import given
import papp

# The kinds of items of the donor that a sentence of Rocq can be.
KINDS = {
    "Definition": ("value", "external", "type"),
    "Fixpoint": ("value",),
    "Inductive": ("type",),
    "Record": ("type",),
    "Module": ("module",),
    "Module Type": ("module type",),
}
HEAD = re.compile(
    r"(Definition|Fixpoint|Inductive|Record|Module\s+Type|Module)\s+(%s)(?![A-Za-z_0-9'.])"
    % papp.PNAME
)

# A line of a Fixpoint whose first word is [with]: its blanks, the name
# after it, and the sign after the name, if they are there.
WITH = re.compile(
    r"(?m)^([ \t]*)with(?![A-Za-z_0-9'.])[ \t]*(?:(%s)(?![A-Za-z_0-9'.])[ \t]*([({:]?))?" % papp.PNAME
)

# A comment that begins with lines of the donor and is no note: the lines,
# then a colon, a semicolon or a comma, then words.
LINES_AND_WORDS = re.compile(r"\(\*\s*(%s)\s*[:;,]" % given.RANGES)

Item = collections.namedtuple("Item", "kind modules name first last whole_first whole_last")

ITEMS = None  # the donor's file -> its items, or the reason why it has none


def plain(name):
    """A name without the [_] that Rocq wants at its end, and a module
    without the [()] of a functor."""
    if name.endswith("()"):
        name = name[:-2]
    return name.rstrip("_") or name


def read_items():
    """decl/DONOR-ITEMS.tsv: for each donor its items, or why it has none;
    and what is wrong with the table."""
    items = collections.defaultdict(list)
    not_read = {}
    wrong = []
    try:
        rows = open(os.path.join(given.DECL, "DONOR-ITEMS.tsv")).read().split("\n")
    except IOError:
        return items, not_read, ["decl/DONOR-ITEMS.tsv is not there"]
    for row in rows:
        if not row:
            continue
        f = row.split("\t")
        if len(f) != 8:
            wrong.append(
                "decl/DONOR-ITEMS.tsv has a row of %d columns, not 8: it is not the table of this tool"
                % len(f)
            )
            break
        if f[1] == "-":
            not_read[f[0]] = f[3]
            continue
        try:
            lines = [int(x) for x in f[4:]]
        except ValueError:
            wrong.append("decl/DONOR-ITEMS.tsv has a row whose lines are no numbers")
            break
        items[f[0]].append(
            Item(f[1], tuple(plain(m) for m in f[2].split(".") if m), f[3], *lines)
        )
    return items, not_read, wrong


class Definition(object):
    """A sentence of a ported file that defines a thing by a name."""

    def __init__(self, pos, end, line, word, name, modules, note):
        self.pos = pos
        self.end = end
        self.line = line
        self.word = word  # Definition, Fixpoint, Inductive, Record, Module, Module Type
        self.name = name
        self.modules = modules  # None: in a functor or a module type of the file
        self.note = note  # the lines of its group, or None
        self.items = []  # the donor's items that it can be
        self.item = None  # the one whose lines the note names
        self.one = False  # [Module X := ..]: one sentence
        self.k = None  # the number of its sentence
        self.run = None  # for the first of a run: the definitions of the run
        self.verdict = None  # the class, for the line of numbers
        self.said = None  # the words of the listing
        self.error = None
        self.clauses = []  # of a Fixpoint: its clauses [with NAME ..]

    def shown(self):
        return "%s %s" % (self.word, self.name)


class Clause(object):
    """A clause [with NAME ..] of a Fixpoint of a ported file."""

    def __init__(self, line, name, fix, note, note_pos, colon):
        self.line = line
        self.name = name
        self.fix = fix  # the Fixpoint
        self.note = note  # the lines of the note directly before it, or None
        self.note_pos = note_pos  # where that note begins
        self.colon = colon  # a comment with lines and a colon stands there
        self.item = None
        self.verdict = None
        self.said = None
        self.error = None

    def shown(self):
        return "with %s (a clause of Fixpoint %s)" % (self.name, self.fix.name)


def lines_of(item):
    return "%d-%d" % (item.first, item.last) if item.first != item.last else "%d" % item.first


def judge(d, donor):
    """The verdict of a definition that the donor has under its name."""
    if d.note is None:
        d.verdict = "no note"
        d.error = "no note of lines stands before it: the donor's %s" % " or ".join(
            "%s %s is %s" % (i.kind, i.name, lines_of(i)) for i in d.items
        )
        return
    named = donor.at(d.note) if len(d.note) == 1 else None
    for i in d.items:
        if named and named == donor.at([(i.first, i.last)]):
            d.item = i
            d.verdict = "the item"
            d.said = "the lines of the donor's %s %s" % (i.kind, i.name)
            return
    for i in d.items:
        whole = (i.whole_first, i.whole_last)
        if whole != (i.first, i.last) and named and named == donor.at([whole]):
            d.item = i
            d.verdict = "the whole item"
            d.said = "the lines of the whole item of the donor that defines the %s %s (its own are %s)" % (
                i.kind,
                i.name,
                lines_of(i),
            )
            return
    d.verdict = "wrong"
    d.error = "the note names %s, and the donor's %s" % (
        given.show(d.note),
        " or ".join(
            "%s %s is %s%s"
            % (
                i.kind,
                i.name,
                lines_of(i),
                " (the whole item %d-%d)" % (i.whole_first, i.whole_last)
                if (i.whole_first, i.whole_last) != (i.first, i.last)
                else "",
            )
            for i in d.items
        ),
    )


def judge_run(run, donor):
    """The verdict of a run of [Module X := ..], by the note before the
    first: its lines are the lines of their items, one after the other."""
    head = run[0]
    head.run = list(run)
    items = [d.items[0] for d in run]
    wanted = []
    for i in items:
        wanted += donor.at([(i.first, i.last)])
    if head.note is not None and len(head.note) == 1 and donor.at(head.note) == wanted:
        for d, i in zip(run, items):
            d.item = i
            d.verdict = "the item" if len(run) == 1 else "a run"
            d.said = (
                "the lines of the donor's module %s" % i.name
                if len(run) == 1
                else "one of the %d modules of the run that begins at line %d: the note before it "
                "names the lines of their items together" % (len(run), head.line)
            )
        return
    for d in run:
        d.verdict = "wrong" if head.note is not None else "no note"
        d.said = "in the run that begins at line %d, whose note is not right" % head.line
    head.said = None
    head.error = "%s, and the donor's %s" % (
        "the note names %s" % given.show(head.note)
        if head.note is not None
        else "no note of lines stands before it",
        ", ".join("module %s is %s" % (i.name, lines_of(i)) for i in items),
    )


def clauses_of(rd, d, whole, errors):
    """The clauses [with NAME ..] of a Fixpoint, each with the note that
    stands directly before it; a line that begins with [with] and that
    the tool does not read is an error."""
    a, b = d.pos, d.end
    margin = a - (rd.text.rfind("\n", 0, a) + 1)
    inside = [c for c in whole if a < c[0] < b]
    out = []
    for m in WITH.finditer(rd.text, a, b):
        at = m.start()
        line = rd.raw.count("\n", 0, at) + 1
        column = len(m.group(1))
        name, sign = m.group(2), m.group(3)
        if column != margin:
            if name and sign:
                errors.append(
                    (
                        line,
                        "a line of %s begins with [with %s %s] at column %d, and the Fixpoint is at column %d: "
                        "a clause is written at the margin of its Fixpoint, and the tool does not read this line"
                        % (d.shown(), name, sign, column, margin),
                    )
                )
            continue
        if not name or not sign:
            errors.append(
                (
                    line,
                    "a line of %s begins with [with] at the margin of the Fixpoint and is not [with NAME (..]: "
                    "the tool does not read it" % d.shown(),
                )
            )
            continue
        note = None
        note_pos = None
        colon = False
        end = at
        for ca, cb in reversed([c for c in inside if c[1] <= at]):
            if rd.raw[cb:end].strip():
                break
            n = given.NOTE.fullmatch(rd.raw[ca:cb])
            if n:
                note, note_pos = given.ranges_of(n.group(1)), ca
                break
            colon = colon or bool(LINES_AND_WORDS.match(rd.raw[ca:cb]))
            end = ca
        out.append(Clause(line, name, d, note, note_pos, colon))
    return out


def judge_clause(c, donor, rows, why):
    """The verdict of a clause [with NAME ..] of a Fixpoint."""
    d = c.fix
    if d.modules is None:
        c.verdict = "functor"
        c.said = "its Fixpoint is in a functor or a module type of the file: not looked up"
        return
    if why:
        c.verdict = "not read"
        c.said = "the donor is not read"
        return
    modules = tuple(plain(x) for x in d.modules)
    named = [i for i in rows if i.kind == "value" and plain(i.name) == plain(c.name) and i.modules == modules]
    if not named:
        c.verdict = "no item"
        c.said = "the donor has no value of that name %s" % ("in %s" % ".".join(modules) if modules else "at its top")
        return
    left = named
    if d.item is not None:
        whole = (d.item.whole_first, d.item.whole_last)
        left = [i for i in named if (i.whole_first, i.whole_last) == whole]
        if not left:
            c.verdict = "wrong"
            c.error = "the donor defines the value %s at %s, not together with %s (the item of lines %d-%d)" % (
                c.name,
                " and ".join(lines_of(i) for i in named),
                d.name,
                whole[0],
                whole[1],
            )
            return
    if len(left) > 1:
        c.verdict = "wrong"
        c.error = "the donor has %d values %s there (%s): the tool cannot tell which one the clause follows" % (
            len(left),
            c.name,
            ", ".join(lines_of(i) for i in left),
        )
        return
    i = left[0]
    if c.note is None:
        c.verdict = "no note"
        c.error = "no note of lines stands directly before it: the donor's definition of %s is %s%s" % (
            i.name,
            lines_of(i),
            " (the comment before it has a colon after its lines: a full stop makes it a note)" if c.colon else "",
        )
        return
    if len(c.note) == 1 and donor.at(c.note) == donor.at([(i.first, i.last)]):
        c.item = i
        c.verdict = "the item"
        c.said = "the lines of the donor's definition of %s" % i.name
        return
    c.verdict = "wrong"
    c.error = "the note names %s, and the donor's definition of %s is %s%s" % (
        given.show(c.note),
        i.name,
        lines_of(i),
        " (the whole item is %d-%d: the note of a clause is the lines of its own definition)"
        % (i.whole_first, i.whole_last)
        if (i.whole_first, i.whole_last) != (i.first, i.last)
        else "",
    )


def check(path, raw=None):
    """The definitions of a ported file, each with its verdict; the
    clauses of its Fixpoints; the notes inside the definitions; the
    errors."""
    global ITEMS
    raw = open(path).read() if raw is None else raw
    rd = given.Reading(path, raw)
    donor = given.donor_of(path)
    if ITEMS is None:
        ITEMS = read_items()
    items, not_read, wrong = ITEMS
    errors = []
    why = donor.why or "; ".join(wrong) or not_read.get(donor.rel)
    if not why and donor.rel not in items:
        why = "decl/DONOR-ITEMS.tsv has no row for %s" % donor.rel
    if why:
        errors.append((1, why))
    definitions = []
    inner = []  # (line, the lines of a note inside a definition, the definition, whether it is inside)
    whole = given.comments(rd.raw)
    for k, (a, b) in enumerate(rd.spans):
        s = rd.text[a:b]
        m = HEAD.match(s)
        if not m:
            continue
        word = " ".join(m.group(1).split())
        d = Definition(
            a,
            b,
            rd.raw.count("\n", 0, a) + 1,
            word,
            m.group(2),
            papp.rocq_modules(rd.text, rd.spans, a),
            rd.begun.get(a) or rd.over.get(a),
        )
        definitions.append(d)
        d.k = k
        d.one = word == "Module" and ":=" in s
        if word == "Fixpoint":
            d.clauses = clauses_of(rd, d, whole, errors)
        if word == "Definition" and rd.bodiless(rd.raw[a:b], k):
            d.verdict = "given"
            d.said = "its OCaml text is given by a directive: make given"
            continue
        if d.modules is None:
            d.verdict = "functor"
            d.said = "in a functor or a module type of the file: not looked up"
            continue
        if why:
            d.verdict = "not read"
            d.said = "the donor is not read"
            continue
        modules = tuple(plain(x) for x in d.modules)
        d.items = [
            i
            for i in items[donor.rel]
            if i.kind in KINDS[word] and plain(i.name) == plain(d.name) and i.modules == modules
        ]
        if not d.items:
            d.verdict = "no item"
            d.said = "the donor has no %s of that name %s" % (
                " or ".join(KINDS[word]),
                "in %s" % ".".join(modules) if modules else "at its top",
            )
            continue
        if d.one:
            continue
        judge(d, donor)
        if d.error:
            errors.append((d.line, "%s: %s" % (d.shown(), d.error)))
        if d.item is None or word not in ("Definition", "Fixpoint"):
            continue
        # the notes inside it
        low, high = d.item.whole_first, d.item.whole_last
        of_clauses = set(c.note_pos for c in d.clauses)
        for ca, cb in whole:
            if a < ca < b and ca not in of_clauses:
                n = given.NOTE.fullmatch(rd.raw[ca:cb]) or LINES_AND_WORDS.match(rd.raw[ca:cb])
                if n:
                    ranges = given.ranges_of(n.group(1))
                    line = rd.raw.count("\n", 0, ca) + 1
                    inside = all(low <= p and q <= high for p, q in ranges)
                    inner.append((line, ranges, d, inside))
                    if not inside:
                        errors.append(
                            (
                                line,
                                "a comment inside %s names %s, outside the lines %d-%d of the donor's item"
                                % (d.shown(), given.show(ranges), low, high),
                            )
                        )
    # the runs of [Module X := ..]: sentences that follow one another with
    # nothing between them, each with one item of the donor
    run = []
    for d in definitions + [None]:
        joins = (
            d is not None
            and d.one
            and len(d.items) == 1
            and run
            and run[-1].k == d.k - 1
            and not rd.raw[rd.spans[d.k - 1][1] + 1:d.pos].strip()
        )
        if run and not joins:
            judge_run(run, donor)
            if run[0].error:
                errors.append((run[0].line, "%s: %s" % (run[0].shown(), run[0].error)))
            run = []
        if d is not None and d.one and d.verdict is None:
            if len(d.items) == 1:
                run.append(d)
            else:
                d.verdict = "wrong"
                d.error = "the donor has %d modules of that name there" % len(d.items)
                errors.append((d.line, "%s: %s" % (d.shown(), d.error)))
    # the clauses of the Fixpoints, after the Fixpoints themselves
    clauses = []
    for d in definitions:
        for c in d.clauses:
            judge_clause(c, donor, items.get(donor.rel, []), why)
            if c.error:
                errors.append((c.line, "%s: %s" % (c.shown(), c.error)))
            clauses.append(c)
    rd.definitions = definitions
    rd.clauses = clauses
    rd.inner = inner
    rd.line_errors = errors
    return rd


def main(files):
    count = collections.Counter()
    clauses = collections.Counter()
    inside = 0
    errors = 0
    listing = os.environ.get("LINES_ALL")
    for path in files:
        rd = check(path)
        for d in rd.definitions:
            count[d.verdict] += 1
        for c in rd.clauses:
            clauses[c.verdict] += 1
        if listing:
            for x in sorted(rd.definitions + rd.clauses, key=lambda x: x.line):
                print(
                    "%s:%d\t%s\t%s\t%s"
                    % (
                        path,
                        x.line,
                        x.shown(),
                        given.show(x.note) if x.note else "no note",
                        x.said or "WRONG: %s" % x.error,
                    )
                )
        inside += len([x for x in rd.inner if x[3]])
        for line, w in sorted(rd.line_errors):
            print("%s:%d: %s" % (path, line, w))
            errors += 1
    right = count["the item"] + count["the whole item"] + count["a run"]
    print(
        "lines: %d definitions in %d files: %d have the note of the lines of the donor's item (%d of them "
        "of the whole item that defines it with others, %d in runs of [Module X := ..]); not judged: %d "
        "whose text a directive gives (make given), %d that the donor has under no such name, %d in a "
        "functor or a module type of the file; %d clauses [with NAME] of a Fixpoint: %d have the note of "
        "the lines of the donor's definition of NAME, %d are not judged; %d notes inside a definition, "
        "each inside the lines of its item; %s"
        % (
            sum(count.values()),
            len(files),
            right,
            count["the whole item"],
            count["a run"],
            count["given"],
            count["no item"],
            count["functor"],
            sum(clauses.values()),
            clauses["the item"],
            clauses["no item"] + clauses["functor"] + clauses["not read"],
            inside,
            "%d wrong" % errors if errors else "nothing wrong",
        )
    )
    return 1 if errors else 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("usage: lines.py FILE.v ...")
    sys.exit(main(sys.argv[1:]))
