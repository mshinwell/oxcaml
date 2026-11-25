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

"""lint.py FILE.v : four cheap checks of a ported file (GUIDE.md, sections 2
and 4): the temporaries of [let!]; Rocq's own [let]; the setters of record
updates (these two at the end of this file); the partial applications of
declared functions (tools/papp.py, which this file calls last). The first:
It COUNTS WORDS, it does not know Rocq's scopes: after the [in] that ends
[let! tmpN := ... in], the word tmpN must stand exactly once before the next
[let! tmpN] or the end of the definition, and [let!] must bind no other name.
The extraction writes the call where the temporary is used: one that is not
used would vanish with its call. What it does not see: where the use is
(under a [fun], in a branch), and a use that is in truth of another variable
of the same name. A label of the kit ([~l:x], which Rocq reads as [x]) is
made blank before the uses are counted, as tools/papp.py reads it (LABELS,
there): the name of a label is no use of a temporary. It follows no file of
the compiler."""
import re, sys
sys.dont_write_bytecode = True
import papp

def strip_comments(s):
    out = []; depth = 0; i = 0; in_str = False
    while i < len(s):
        if depth == 0 and s[i] == '"':
            in_str = not in_str; out.append(' '); i += 1; continue
        if in_str:
            out.append('\n' if s[i] == '\n' else ' '); i += 1; continue
        if s.startswith('(*', i): depth += 1; i += 2; out.append('  '); continue
        if depth and s.startswith('*)', i): depth -= 1; i += 2; out.append('  '); continue
        out.append(s[i] if depth == 0 or s[i] == '\n' else ' '); i += 1
    return ''.join(out)

path = sys.argv[1]
text = strip_comments(open(path).read())
# the same text with each label of the kit made blank, for the count of the
# uses of a temporary
unlabelled = papp.without_labels(text)
bad = 0
def line_of(pos): return text.count('\n', 0, pos) + 1
binds = list(re.finditer(r"let!\s+([A-Za-z_][A-Za-z_0-9']*)\s*:=", text))
for n, m in enumerate(binds):
    name = m.group(1)
    if not re.fullmatch(r"tmp[0-9]+", name):
        print("%s:%d: let! binds %s: only tmp1, tmp2, ..." % (path, line_of(m.start()), name)); bad += 1
        continue
    # the scope: up to the next binding of the same name, or the end of the
    # definition (a full stop that ends a line)
    end = len(text)
    for m2 in binds[n + 1:]:
        if m2.group(1) == name: end = m2.start(); break
    stop = re.compile(r"\.\s*\n").search(text, m.end())
    if stop and stop.start() < end: end = stop.start()
    # the body: after the [in] that ends the right side (outside brackets)
    depth = 0; body = None
    for m3 in re.finditer(r"[()]|(?<![A-Za-z_0-9'.])in(?![A-Za-z_0-9'])", text[m.end():end]):
        if m3.group(0) == "(": depth += 1
        elif m3.group(0) == ")": depth -= 1
        elif depth == 0: body = m.end() + m3.end(); break
    if body is None:
        print("%s:%d: no [in] found for let! %s" % (path, line_of(m.start()), name)); bad += 1
        continue
    uses = len(re.findall(r"(?<![A-Za-z_0-9'.])%s(?![A-Za-z_0-9'])" % name, unlabelled[body:end]))
    if uses != 1:
        print("%s:%d: %s is used %d times: a let! is used exactly once" % (path, line_of(m.start()), name, uses)); bad += 1
# Rocq's own [let x := e in] (not [let*], [let&], [let!]): the extraction
# moves [e] to the use of [x], or drops it. The guide allows it for a local
# recursion ([fix]) and for a local function ([fun]) only.
for m in re.finditer(r"(?<![A-Za-z_0-9'.])let\s+([A-Za-z_][A-Za-z_0-9']*)\s*(?::[^:=]*)?:=\s*(\S+)", text):
    if m.group(2) not in ("fix", "fun"):
        print("%s:%d: Rocq's own let of %s: only a fix or a fun may be bound so (use let* for a call, let& for a value)" % (path, line_of(m.start()), m.group(1))); bad += 1

# The setters of record updates (GUIDE.md, section 4). The OCaml text of
#   Extract Inlined Constant update_X => "(fun t p1 .. -> { t with F1 = p1; .. })".
# is not checked by Rocq against
#   Definition update_X (t : T) (p1 : ..) .. : T := {| .. |}.
# so it is checked here, as words: the record of the definition gives the
# fields F1 .. the parameters p1 .. in that order, and every other field g is
# [g := t.(g)]. Names are compared without the underscores that end them.
raw = open(path).read()
# The last part of a name; a Rocq field may have underscores after it where
# Rocq's one name space needs them ([handlers__] for OCaml's [handlers]).
def last(name): return name.strip().split(".")[-1].rstrip("_")
for m in re.finditer(r'Extract\s+Inlined\s+Constant\s+(update_[A-Za-z_0-9\']*)\s*=>\s*"([^"]*)"\s*\.', raw):
    name = m.group(1); txt = re.sub(r"\s+", " ", m.group(2)).strip()
    where = "%s:%d: setter %s" % (path, raw.count("\n", 0, m.start()) + 1, name)
    t = re.fullmatch(r"\(fun t((?: [a-z_][A-Za-z_0-9']*)+) -> \{ t with (.*) \}\)", txt)
    if not t:
        print("%s: its text is not (fun t p1 .. -> { t with F1 = p1; .. })" % where); bad += 1; continue
    xs = t.group(1).split(); sets = [x.split("=") for x in t.group(2).split(";")]
    if "t" in xs or len(set(xs)) != len(xs) or len(sets) != len(xs) \
       or any(len(x) != 2 or x[1].strip() != xs[i] for i, x in enumerate(sets)):
        print("%s: its text must set one field to each of its parameters after t, in order" % where); bad += 1; continue
    fields = [last(x[0]) for x in sets]
    d = re.search(r"(?<![A-Za-z_0-9'.])Definition\s+%s(?![A-Za-z_0-9'])" % re.escape(name), text)
    if not d:
        print("%s: no Definition of that name" % where); bad += 1; continue
    stop = text.find(":=", d.end()); o = text.find("{|", stop); c = text.find("|}", o)
    if stop < 0 or o < 0 or c < 0 or text[stop + 2:o].strip():
        print("%s: its Definition is not one record {| .. |}" % where); bad += 1; continue
    # the binders: the names before a colon at the first depth of brackets
    binders = []; depth = 0
    for b in re.finditer(r"[()]|([A-Za-z_][A-Za-z_0-9']*)\s*:", text[d.end():stop]):
        if b.group(0) == "(": depth += 1
        elif b.group(0) == ")": depth -= 1
        elif depth == 1: binders.append(b.group(1))
    if len(binders) != len(xs) + 1:
        print("%s: the Definition has %d parameters after the record, the text has %d" % (where, len(binders) - 1, len(xs))); bad += 1; continue
    base = binders[0]; given = {}
    for f in text[o + 2:c].split(";"):
        if ":=" not in f: continue
        g, e = f.split(":=", 1); given[last(g)] = re.sub(r"\s+", "", e)
    for i, f in enumerate(fields):
        if given.get(f) != binders[i + 1]:
            print("%s: the text sets %s to the parameter %d, the Definition gives it %s" % (where, f, i + 1, given.get(f))); bad += 1
    for g, e in given.items():
        if g in fields: continue
        k = re.fullmatch(r"%s\.\(([A-Za-z_0-9'.]+)\)" % re.escape(base), e)
        if not k or last(k.group(1)) != g:
            print("%s: the Definition changes the field %s (%s), the text does not" % (where, g, e)); bad += 1
# The partial applications of declared functions (GUIDE.md, section 2):
# each [pappN F] against decl/ARITIES.tsv, and the marks PORT-GAP(papp).
# tools/papp.py says what is checked and what is not.
papp_lines, papp_bad = papp.check(path, raw)
for l in papp_lines: print(l)
bad += papp_bad
sys.exit(1 if bad else 0)
