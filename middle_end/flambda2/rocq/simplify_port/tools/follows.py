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

"""follows.py FILE.v ... : the first comment of a ported file names the file
of the compiler that it follows (its donor) and the TEXT of the donor that
it follows; this compares both with the tree. Run in the folder of the port
(the Makefile's target follows, a part of check). It follows no file of the
compiler.

DIR/Foo.v follows middle_end/flambda2/simplify/DIR/foo.ml. After the
donor's header it has one comment that begins, at the left margin,

    (* This file follows PATH (Git blob ID)

where PATH is the donor from the root of the repository and ID is the name
that Git gives the bytes of a file (`git hash-object FILE` prints it: the
SHA-1 of the word blob, the length and the bytes). The words may stand on
several lines. If the file has abbreviations of modules of its own, the file
abbrev/foo/Port_abbreviations.v begins with the same words about the same
donor.

For each FILE.v given, and for its file of abbreviations if there is one,
the tool says
  - if the comment is not there in that form;
  - if PATH is not the donor of the file;
  - if ID is not the name of the donor's text in the tree: THE DONOR HAS
    CHANGED since the file was last said to follow it. The change is then
    read and carried over to the file, and the new name written (that of
    the tree, which the tool prints).
It also says if a directory of abbrev/ is of no file that was given. The
exit status is 1 if it said anything.

So a commit can change a donor and its ported file together, and after it
the comment is true: the name is of the text, not of a commit. WHAT IT DOES
NOT SAY: that the file follows the donor (make given and make lines compare
texts and lines; the reading compares the rest). It says that not one byte
of the donor has changed since someone wrote that name."""
import hashlib
import os
import re
import sys

SIMPLIFY = os.path.join("..", "..", "simplify")
FORM = re.compile(r"\(\* This file follows (\S+) \(Git blob ([0-9a-f]{40})\)")


def blob(data):
    """The name that Git gives these bytes as the content of a file."""
    return hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()


def named(path):
    """The donor and the text that the first comment of a file names, or None."""
    with open(path, errors="replace") as f:
        lines = f.read().split("\n")
    for i, line in enumerate(lines):
        if line.startswith("(* This file follows"):
            # the path and the name are within the first lines of the comment
            m = FORM.match(" ".join(" ".join(lines[i : i + 6]).split()))
            return m.groups() if m else None
    return None


def donor_of(v):
    """DIR/Foo.v: the donor from the root of the repository, and from here."""
    d, base = os.path.split(v)
    rel = os.path.join(d, base[:-2].lower() + ".ml")
    return "middle_end/flambda2/simplify/" + rel, os.path.join(SIMPLIFY, rel)


def check(path, donor, here, said):
    """One file against its donor; the complaints go to [said]."""
    if not os.path.isfile(here):
        said.append("%s: its donor %s is not there" % (path, donor))
        return
    with open(here, "rb") as f:
        now = blob(f.read())
    found = named(path)
    if found is None:
        said.append(
            "%s: no comment at the left margin that begins `(* This file follows PATH (Git blob ID)`; "
            "its donor is %s, whose text in the tree is the blob %s" % (path, donor, now)
        )
    elif found[0] != donor:
        said.append("%s: it says that it follows %s; its donor is %s" % (path, found[0], donor))
    elif found[1] != now:
        said.append(
            "%s: it follows %s as the text that Git names %s; the tree has another text of that file "
            "(%s): THE DONOR HAS CHANGED. Carry the change over, then write the new name" % (path, donor, found[1], now)
        )


def main(files):
    said = []
    abbrevs = 0
    seen = set()
    for v in files:
        donor, here = donor_of(v)
        check(v, donor, here, said)
        name = os.path.basename(v)[:-2].lower()
        seen.add(name)
        a = os.path.join("abbrev", name, "Port_abbreviations.v")
        if os.path.isfile(a):
            abbrevs += 1
            check(a, donor, here, said)
    if os.path.isdir("abbrev"):
        for name in sorted(os.listdir("abbrev")):
            if name not in seen and os.path.isdir(os.path.join("abbrev", name)):
                said.append("abbrev/%s: no file that was given has that name" % name)
    for line in said:
        print("follows: " + line)
    print(
        "follows: %d ported files and %d files of abbrev/: %s"
        % (
            len(files),
            abbrevs,
            "each names its donor and the text of it that the tree has" if not said else "%d things said above" % len(said),
        )
    )
    return 1 if said else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
