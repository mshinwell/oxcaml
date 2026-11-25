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

"""shells.py [FILE ...] : every shell script has the line `set -eu` before
its first command, so that it stops at a command that fails and at a
variable that is not set. Run in the folder of the port. With no FILE: every
file of the folder (not what is under _build/). It follows no file of the
compiler.

A file is a shell script if its name ends `.sh`, or if its first line names
a shell (`#!/bin/bash`, `#!/bin/sh`, or one of the two through
`/usr/bin/env`). Its first command is its first line that is not blank and
is not a comment (a line that begins `#`); that line must be `set -eu` and
no more.

It prints the number of shell scripts, and each one that does not begin so,
with its first command. The exit status is 1 if there is one.

WHAT IT DOES NOT SAY: that a script is right under `set -eu` (that each
command which may fail on purpose is in a test, and each variable that may
be left out has a default): that is read, and the script is run. It does not
read the lines of shell inside the Makefile or inside another file."""
import os
import sys

SHELLS = ("#!/bin/bash", "#!/bin/sh", "#!/usr/bin/env bash", "#!/usr/bin/env sh")


def lines_if_shell(path):
    """The lines of a file if it is a shell script; None if it is not."""
    with open(path, errors="replace") as f:
        first = f.readline()
        if not (path.endswith(".sh") or first.replace("#! ", "#!").strip() in SHELLS):
            return None
        return [first.rstrip("\n")] + f.read().split("\n")


def first_command(lines):
    for line in lines:
        s = line.strip()
        if s and not s.startswith("#"):
            return line.rstrip()
    return ""


def files_of_folder():
    out = []
    for d, dirs, files in os.walk("."):
        dirs[:] = sorted(x for x in dirs if not (d == "." and x == "_build"))
        out += [os.path.join(d, f)[2:] for f in sorted(files)]
    return out


def main(paths):
    n = bad = 0
    for path in paths or files_of_folder():
        if not os.path.isfile(path):
            continue
        lines = lines_if_shell(path)
        if lines is None:
            continue
        n += 1
        first = first_command(lines)
        if first != "set -eu":
            bad += 1
            what = "it has no command" if first == "" else "its first command is `%s`" % first
            print("shells: %s: %s, not `set -eu`" % (path, what))
    print("shells: %d shell scripts: %s" % (n, "each has `set -eu` before its first command" if bad == 0 else "%d without `set -eu` before the first command" % bad))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
