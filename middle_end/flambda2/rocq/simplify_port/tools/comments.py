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

"""comments.py SIMPLIFY_DIR [FILE.v ...] : what a ported file must carry over
from the file that it follows, as text (GUIDE.md, section 1). Run in the
folder of the port. For each DIR/foo.ml of SIMPLIFY_DIR that has a
DIR/Foo.v (or for the .v files named), it says
  - if the leading notice of the .v file is not that of the .ml file,
    character for character;
  - each comment of the .ml file after the notice whose words are not in
    the .v file (spaces and line breaks aside), with its line. A comment
    that begins CR or XCR is not asked for.
It compares texts only: it does not know WHERE in the .v file a comment
stands. The exit status is 1 if it said anything. It follows no file of the
compiler."""
import os, re, sys

def comments(s):
    """The comments of an OCaml text that are not inside another: (line, text)."""
    out = []; i = 0; n = len(s); depth = 0; start = 0
    while i < n:
        if depth == 0 and s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            i = j + 1; continue
        if depth == 0 and s[i] == "'" and i + 2 < n:
            if s[i + 1] != '\\' and s[i + 2] == "'": i += 3; continue
            if s[i + 1] == '\\':
                j = s.find("'", i + 2)
                if 0 <= j <= i + 5: i = j + 1; continue
        if s.startswith("(*", i) and not s.startswith("(*)", i):
            if depth == 0: start = i
            depth += 1; i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; i += 2
            if depth == 0: out.append((s.count("\n", 0, start) + 1, s[start:i]))
            continue
        i += 1
    return out

def notice(text):
    """The leading notice: the comments that begin the file, each on the
    line after the one before (a box of one comment a line, or one long
    comment), as one text; None if the file does not begin with a comment."""
    end = 0
    for _, c in comments(text):
        if text.startswith(c, end): end += len(c)
        elif text.startswith("\n" + c, end) and end > 0: end += 1 + len(c)
        else: break
    return text[:end] if end else None

norm = lambda t: re.sub(r"\s+", " ", t).strip()

simplify = sys.argv[1]
only = set(os.path.normpath(a) for a in sys.argv[2:])
said = 0; files = 0
for d, _, fs in sorted(os.walk(simplify)):
    for f in sorted(fs):
        if not f.endswith(".ml"): continue
        rel = os.path.relpath(os.path.join(d, f), simplify)
        v = os.path.normpath(os.path.join(os.path.dirname(rel), f[0].upper() + f[1:-3] + ".v"))
        if not os.path.exists(v) or (only and v not in only): continue
        files += 1
        donor = open(os.path.join(d, f)).read(); port = open(v).read()
        if notice(donor) is not None and notice(port) != notice(donor):
            print("%s: the leading notice is not that of %s" % (v, rel)); said += 1
        words = norm(port)
        after = (notice(donor) or "").count("\n") + 1
        for line, c in comments(donor):
            if line <= after: continue
            body = norm(c[2:-2]).lstrip("* ").strip()
            if not body or re.match(r"X?CR\b", body): continue
            if norm(c[2:-2]) not in words and body not in words:
                print("%s: comment of line %d of %s: %s" % (v, line, rel, norm(c)[:60])); said += 1
print("%d files; %d things said" % (files, said))
sys.exit(1 if said else 0)
