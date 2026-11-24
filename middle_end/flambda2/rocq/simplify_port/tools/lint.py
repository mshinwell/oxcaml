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

"""lint.py FILE.v : one cheap check of a ported file (GUIDE.md, section 2):
every temporary that [let! tmpN := ... in] binds is used exactly once before
it is bound again or its definition ends, and [let!] binds no other name. The
extraction writes the call where the temporary is used: one that is not used
would vanish with its call. It does not see where the use is (under a [fun],
in a branch). It follows no file of the compiler."""
import re, sys

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
    uses = len(re.findall(r"(?<![A-Za-z_0-9'.])%s(?![A-Za-z_0-9'])" % name, text[m.end():end]))
    if uses != 1:
        print("%s:%d: %s is used %d times: a let! is used exactly once" % (path, line_of(m.start()), name, uses)); bad += 1
sys.exit(1 if bad else 0)
