#!/bin/bash
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

# [DUNE=..] [JOBS=N] typedtrees.sh : THE TYPED TREES THAT THE TOOLS OF THE
# PORT READ, WITHOUT BUILDING THE COMPILER. It follows no file of the
# compiler.
#
# WHAT IT IS FOR. The tools of the port read a build of the compiler: its
# compiled interfaces and typed trees (tools/declgen/run.sh BUILD_ROOT,
# which makes decl/; make CMI_ROOT=BUILD_ROOT; tools/gate.sh BUILD_ROOT).
# When the compiler changes, the port follows: decl/ is made again from a
# build of the changed compiler, and the ported files are mended. Once the
# build of the compiler compiles the extracted files of the port, a
# change of an INTERFACE that an extracted file uses, and that the file
# no longer fits, stops that build until the port has followed, and the
# port cannot follow without a build. (A change of an implementation
# alone does not stop it.) This script makes the part of the build that
# the tools read. It compiles no file of the port, links no compiler, and
# takes about half a minute from nothing.
#
# WHAT IT RUNS, at the root of the work tree in which this folder is. The
# tree must be configured (./configure, as for a build of the compiler),
# and the programs that `make boot-compiler` needs must be on the PATH.
#   make _build/_bootinstall
#       writes the small files that the root dune file includes; it starts
#       no dune and builds nothing;
#   DUNE build -j JOBS @DIR/check ... ocamlcommon.cma ocamlfrontend.cma
#       oxcaml_common.cma
#       ONE command of dune: the alias `check` of each directory of the
#       list below (the compiled interfaces and the typed trees of its
#       library, no program), and the bytecode archives of three
#       libraries of the root directory.
# After it ROOT/_build/default is the BUILD_ROOT for the tools.
#
# THE LIST is the load path of the library of Simplify: the directories
# that dune gives with -I to the compiler when it compiles a file of
# middle_end/flambda2/simplify. They are that library's own directory; the
# libraries that its dune file names and those that they need (16 more
# directories under middle_end/flambda2, 5 under backend); and three
# libraries of the root directory, which have no directory of their own
# and are asked for by their archives. The generator of decl/ finds the
# compiled files of the units that Simplify uses on that path.
#
# IF THE LIST HAS BECOME TOO SHORT (Simplify uses a library that is not in
# it; a library has moved), THE GENERATOR SAYS SO: it writes no file, ends
# with status 2, and names each unit of which it does not find the typed
# tree (decl/README.md). TO LENGTHEN THE LIST: find the source of a unit
# that is named (FILE.ml, where FILE is the name of the unit after its
# last `__`, in small letters); add its directory to one of the two lists
# below; if its library is of the root directory (its stanza is in the
# root dune file), add the bytecode archive of the library instead. Run
# the script and the generator again.
#
# DUNE: the words that start dune (`dune` if not given), for example
# DUNE="nice -n 10 /path/to/dune". JOBS: the number for dune's -j (4 if not
# given). Exit status: 0 if the two commands end well; 2 if the tree is
# not configured; else the status of the command that failed.
set -eu
here=$(dirname "$0")
root=$(cd "$here/../../../../.." && pwd)
if [ ! -e "$root/Makefile.config" ]; then
  echo "typedtrees.sh: $root is not configured (no Makefile.config): run ./configure there first" >&2
  exit 2
fi
DUNE=${DUNE:-dune}; JOBS=${JOBS:-4}
targets=@middle_end/flambda2/simplify/check
for d in algorithms bound_identifiers classic_mode_types cmx datalog \
  identifiers import kinds lattices nominal numbers simplify_shared \
  term_basics terms types ui; do
  targets="$targets @middle_end/flambda2/$d/check"
done
for d in arm64/ast arm64/binary_emitter asm_targets binary_emitter_intf \
  debug/dwarf/dwarf_flags; do
  targets="$targets @backend/$d/check"
done
targets="$targets ocamlcommon.cma ocamlfrontend.cma oxcaml_common.cma"
cd "$root"
make _build/_bootinstall
# $DUNE and $targets are lists of words: each word is one argument
$DUNE build -j "$JOBS" $targets
echo "typedtrees.sh: $root/_build/default has the typed trees that the tools of the port read"
