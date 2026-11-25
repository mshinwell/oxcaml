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

# gate.sh BUILD_ROOT [LOG_DIR] : THE GATE OF THE PORT, as one command. It
# follows no file of the compiler.
#
# BUILD_ROOT is the _build/default of a dune build of the compiler from the
# sources of this tree (its compiled interfaces and typed trees are read;
# nothing is written there). The command works in the folder of the port,
# wherever it is called from. THE TREE MUST HAVE ONLY ITS TRACKED FILES IN
# THE FOLDER, as a new work tree has (git clean -xdn . shows what else is
# there). It needs git, make, Rocq, OCaml (with ocamlfind and the compiler's
# library, for tools/declgen), ocamlformat and Python on the PATH; ROCQ,
# OCAMLC and PYTHON in the environment name other programs, as for make.
# ocamlformat is called by that name: the variable OCAMLFORMAT of the
# environment is ocamlformat's own, for its options.
#
# It prints each thing that it asks with the answer, one line each
# ("gate: (N) ...: yes" or "... : NO", with what was found), and then PASSED
# or FAILED. Exit status 0 only if every answer is yes; 1 if one is NO; 2 if
# it was not given a build root, or if it may not write in the place of the
# logs (below): then it has asked nothing. One process at a time (make -j1).
#
# WHAT IT ASKS:
#  (1) before anything is made, the folder has only tracked files, none of
#      them changed, and no _build (git status --porcelain --ignored);
#  (2) decl/ made again from BUILD_ROOT by tools/declgen/run.sh, in LOG_DIR,
#      is the decl/ of the tree: the same files, README.md apart, which is
#      written by hand, with the same bytes;
#  (3) each file that a file of decl/ says it follows has, in the commit,
#      the text that the file of decl/ names (its Git blob);
#  (4) the tracked .ml files under extracted/ are those of `make list`, and
#      the only other file there is .ocamlformat; the same on the disk;
#  (5) the tracked .ml files under runtime/ are port_monad.ml and
#      port_abbreviations.ml, and the only other file there is .ocamlformat;
#      the same on the disk;
#  (6) the folder's dune file, its comments taken out, is the one stanza
#      (include_subdirs no);
#  (7) no other file named dune, dune-project, dune-workspace or *.opam is
#      in the folder, tracked or on the disk;
#  (8) every .ml and .mli file of the folder for which ocamlformat is not
#      disabled (ocamlformat --print-config) is as ocamlformat leaves it
#      (ocamlformat --check);
#  (9) every tracked file of the folder that is a shell script (by its
#      name *.sh, or by its first line) has the line `set -eu` before its
#      first command (tools/shells.py);
# (10) make, from nothing, exits 0 (it says how long the make took);
# (11) after the make, git status --porcelain of the folder is empty: the
#      extracted files and PROGRESS.md are made again as they are committed;
# (12) after the make, the files on the disk under extracted/ and runtime/
#      are the tracked ones, and (7) holds on the disk;
# (13) after the make, git status --porcelain --ignored of the folder shows
#      _build/ and nothing else: the make left nothing in the folder but
#      that directory (the Makefile lets Python write no compiled copy of
#      the tools beside them), so whoever removes _build/ after the gate
#      has the tree as it was.
# The make is the long part (about 25 minutes). It is NOT RUN if an answer
# before it is NO, and the gate has then failed: (10) to (13) say "not
# asked".
#
# WHAT IT DOES NOT ASK: whether a range of commits changes a path outside
# the folder; who made the commits and how their subjects read; which words
# the texts use. The programs are named with their versions and not judged.
#
# THE PLACE OF THE LOGS is the second argument, LOG_DIR. It is made if it is
# not there. If it is not given, a new directory is made under the
# temporary directory (TMPDIR, or /tmp); the second line that the gate
# prints names it. It keeps decl.log, the decl/ that was made (decl/), the
# generator as it was compiled (declgen/), shells.log and make.log. What an
# earlier run of the gate left there under these names is removed first, so
# the gate can be called again with the same LOG_DIR; to keep the logs of
# several commits, give each call its own. In the folder of the port the
# gate removes nothing: the _build of its make stays, and before the gate
# is called again in the same tree it must be removed (1).
#
# THE GATE REFUSES A PLACE OF THE LOGS IN WHICH IT COULD REMOVE OR WRITE
# WHAT IS NOT ITS OWN, BEFORE IT MAKES OR REMOVES ANYTHING (exit status 2).
# Four directories are kept from it: the work tree of the repository, the
# directory of Git of that work tree, the directory of Git of the
# repository, and the build root. The place of the logs may not be one of
# them, nor be in one, nor hold one (what is removed first, LOG_DIR/decl,
# could be it). Each path is compared as it is without its symbolic links,
# so a link to such a place is refused too. A temporary directory that is
# one of the four, or in one, is refused in the same way.
set -eu
if [ $# -lt 1 ] || [ ! -d "$1/middle_end/flambda2/simplify/.flambda2_simplify.objs/byte" ]; then
  echo "usage: tools/gate.sh BUILD_ROOT [LOG_DIR]"
  echo "  BUILD_ROOT: the _build/default of a dune build of the compiler from the sources of this tree"
  exit 2
fi
ROCQ=${ROCQ:-rocq}; OCAMLC=${OCAMLC:-ocamlc.opt}; PYTHON=${PYTHON:-python3}
# physical PATH : the path without its symbolic links, whether or not
# something is there
physical() { "$PYTHON" -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$1"; }
# within A B : is the path A the path B, or under it (two physical paths)
within() { local a=${1%/} b=${2%/}; case "$a/" in "$b/"*) return 0;; esac; return 1; }
build=$(physical "$1")
if [ $# -ge 2 ]; then given=yes; logs=$(physical "$2"); else given=no; logs=$(physical "${TMPDIR:-/tmp}"); fi
cd "$(dirname "$0")/.."
tree=$(git rev-parse --show-toplevel); tree=$(physical "$tree")
# of_git OPTION : the directory that git rev-parse OPTION names, asked at
# the top of the work tree
of_git() { (cd "$tree" && d=$(git rev-parse "$1") && physical "$d"); }
gitdir=$(of_git --git-dir); common=$(of_git --git-common-dir)
# kept WHAT PATH : PATH is one of the four directories; if the place of the
# logs is refused for it, why. A temporary directory that holds one of them
# is not refused: the new directory that is made in it holds nothing.
why=""
kept() {
  if within "$logs" "$2"; then why="it is $1, $2, or is in it"
  elif [ $given = yes ] && within "$2" "$logs"; then why="$1, $2, is in it"; fi
}
kept "the work tree of the repository" "$tree"
kept "the directory of Git of the work tree" "$gitdir"
kept "the directory of Git of the repository" "$common"
kept "the build root" "$build"
if [ -n "$why" ]; then
  if [ $given = yes ]; then what="the place of the logs"; else what="the temporary directory"; fi
  echo "gate: $what $logs is refused: $why. Nothing was made or removed."
  exit 2
fi
if [ $given = yes ]; then mkdir -p "$logs"; else logs=$(mktemp -d "$logs/tmp.XXXXXXXXXX"); fi
rm -rf "$logs/decl" "$logs/declgen"
rm -f "$logs/decl.log" "$logs/decl.made" "$logs/decl.tracked" "$logs/shells.log" "$logs/make.log"
no=0
# answer N WHAT yes|NO [FOUND] : one line; counts the answers NO
answer() {
  if [ "$3" = yes ]; then echo "gate: ($1) $2: yes${4:+ ($4)}"
  else echo "gate: ($1) $2: NO${4:+: $4}"; no=$((no+1)); fi
}
# one_line : the lines of the standard input on one line, the first 8
one_line() { head -8 | tr '\n' ' ' | sed 's/ *$//'; }
# version PROGRAM ARGUMENT... : where the program is, and the first line of
# what it prints with the arguments
version() {
  local where what
  if where=$(command -v "$1"); then
    what=$("$@" 2>&1 | head -1) || what="(it does not say)"
    echo "gate: $1 is $where; \"$*\" prints: $what"
  else
    echo "gate: $1: NOT FOUND on the PATH"; no=$((no+1))
  fi
}
echo "gate: the commit of the tree is $(git rev-parse HEAD); the folder is $(pwd)"
echo "gate: the build root is $build; the logs are in $logs"
version "$ROCQ" --version
version "$OCAMLC" -version
version ocamlfind ocamlopt -version
version ocamlformat --version
version "$PYTHON" --version
version make --version
version git --version

# (1)
found=$(git status --porcelain --ignored -- . | one_line)
if [ -z "$found" ]; then a=yes; else a=NO; fi
answer 1 "before anything is made, the folder has only tracked files, none changed, and no _build" $a "$found"

# (2)
rc=0
DECL_OUT="$logs/decl" DECLGEN_BUILD="$logs/declgen" tools/declgen/run.sh "$build" > "$logs/decl.log" 2>&1 || rc=$?
if [ -d "$logs/decl" ]; then ls "$logs/decl" | LC_ALL=C sort > "$logs/decl.made"; else : > "$logs/decl.made"; fi
git ls-files decl | sed 's|^decl/||' | grep -v '^README\.md$' | LC_ALL=C sort > "$logs/decl.tracked" || true
only_made=$(LC_ALL=C comm -23 "$logs/decl.made" "$logs/decl.tracked" | one_line)
only_tree=$(LC_ALL=C comm -13 "$logs/decl.made" "$logs/decl.tracked" | one_line)
differ=0; differing=""
for f in $(LC_ALL=C comm -12 "$logs/decl.made" "$logs/decl.tracked"); do
  if ! cmp -s "$logs/decl/$f" "decl/$f"; then differ=$((differ+1)); differing="$differing $f"; fi
done
found="$(wc -l < "$logs/decl.made") files made, $(wc -l < "$logs/decl.tracked") in the tree; $differ differ"
found="$found; only made: ${only_made:-none}; only in the tree: ${only_tree:-none}"
if [ $rc != 0 ]; then
  said=$(grep -A 2 '^declgen: ' "$logs/decl.log" | one_line) || true
  found="tools/declgen/run.sh exits $rc: ${said:-$(tail -1 "$logs/decl.log")}; $found"
fi
if [ $differ != 0 ]; then found="$found; the first that differ:$(echo "$differing" | cut -d' ' -f1-6)"; fi
if [ $rc = 0 ] && [ $differ = 0 ] && [ -z "$only_made" ] && [ -z "$only_tree" ] && [ -s "$logs/decl.made" ]; then a=yes; else a=NO; fi
answer 2 "decl/ made again from the build root is the decl/ of the tree, README.md apart" $a "$found"

# (3)
n=0; bad=0; which=""
for f in $(git ls-files 'decl/*.v'); do
  n=$((n+1))
  blob=$(sed -n 's/^   (Git blob \([0-9a-f]\{40\}\)).*$/\1/p' "$f")
  path=$(awk '/^   \(Git blob [0-9a-f]+\)/ { print prev; exit } { prev = $0 }' "$f" | sed 's/^ *//')
  have=$(git rev-parse --verify -q "HEAD:$path" 2> /dev/null) || have=none
  if [ -z "$blob" ] || [ "$blob" != "$have" ]; then bad=$((bad+1)); which="$which $f"; fi
done
if [ $bad = 0 ] && [ $n -gt 0 ]; then a=yes; found="$n files"; else a=NO; found="$bad of $n files:$(echo "$which" | cut -d' ' -f1-6)"; fi
answer 3 "each file that a file of decl/ says it follows has, in the commit, the text (Git blob) that the file of decl/ names" $a "$found"

# (4) and (5)
# on_disk DIR : are the files on the disk under DIR the tracked ones
on_disk() {
  [ "$(find "$1" -type f | LC_ALL=C sort)" = "$(git ls-files "$1" | LC_ALL=C sort)" ]
}
listed=$(make -s list | cut -f3 | LC_ALL=C sort)
tracked=$(git ls-files extracted | grep '\.ml$' | LC_ALL=C sort) || true
others=$(git ls-files extracted | grep -v '\.ml$' | one_line) || true
found="$(echo "$tracked" | grep -c . || true) tracked .ml files, $(echo "$listed" | grep -c . || true) lines of make list; the other tracked files: ${others:-none}"
if [ "$listed" = "$tracked" ] && [ -n "$tracked" ] && [ "$others" = extracted/.ocamlformat ] && on_disk extracted; then a=yes
else a=NO; found="$found; on the disk and not tracked, or tracked and not on the disk: $( { find extracted -type f; git ls-files extracted; } | LC_ALL=C sort | uniq -u | one_line)"; fi
answer 4 "the tracked .ml files under extracted/ are those of make list, the one other file there is .ocamlformat, and the disk has the same files" $a "$found"
tracked=$(git ls-files runtime | grep '\.ml$' | LC_ALL=C sort | one_line) || true
others=$(git ls-files runtime | grep -v '\.ml$' | one_line) || true
found="the tracked .ml files: ${tracked:-none}; the other tracked files: ${others:-none}"
if [ "$tracked" = "runtime/port_abbreviations.ml runtime/port_monad.ml" ] && [ "$others" = runtime/.ocamlformat ] && on_disk runtime; then a=yes
else a=NO; found="$found; on the disk and not tracked, or tracked and not on the disk: $( { find runtime -type f; git ls-files runtime; } | LC_ALL=C sort | uniq -u | one_line)"; fi
answer 5 "the tracked .ml files under runtime/ are port_monad.ml and port_abbreviations.ml, the one other file there is .ocamlformat, and the disk has the same files" $a "$found"

# (6): a comment of dune is from a semicolon to the end of the line
stanzas=$(sed 's/;.*$//' dune | tr -s ' \t\n' '   ' | sed 's/^ //; s/ $//; s/( /(/g; s/ )/)/g')
if [ "$stanzas" = "(include_subdirs no)" ]; then a=yes; found=""; else a=NO; found="it is: $(echo "$stanzas" | cut -c1-200)"; fi
answer 6 "the folder's dune file, its comments taken out, is the one stanza (include_subdirs no)" $a "$found"

# (7)
# of_dune : the paths of the standard input that dune or opam would read
of_dune() { grep -E '(^|/)(dune|dune-project|dune-workspace)$|\.opam$' | LC_ALL=C sort | one_line || true; }
tracked=$(git ls-files | of_dune)
disk=$(find . -type f | sed 's|^\./||' | of_dune)
if [ "$tracked" = dune ] && [ "$disk" = dune ]; then a=yes; found=""; else a=NO; found="tracked: ${tracked:-none}; on the disk: ${disk:-none}"; fi
answer 7 "no other file named dune, dune-project, dune-workspace or *.opam is in the folder, tracked or on the disk" $a "$found"

# (8)
all=0; on=0; bad=0; which=""
for f in $(git ls-files | grep -E '\.mli?$' | LC_ALL=C sort); do
  all=$((all+1))
  if ocamlformat --print-config "$f" 2>&1 | grep -q '^disable=false'; then
    on=$((on+1))
    if ! ocamlformat --check "$f" > /dev/null 2>&1; then bad=$((bad+1)); which="$which $f"; fi
  fi
done
if [ $bad = 0 ] && [ $on -gt 0 ]; then a=yes; found="$on of the $all .ml and .mli files"
else a=NO; found="$bad of the $on for which it is not disabled ($all .ml and .mli files):$(echo "$which" | cut -d' ' -f1-6)"; fi
answer 8 "every .ml and .mli file of the folder for which ocamlformat is not disabled is as ocamlformat leaves it" $a "$found"

# (9)
rc=0
git ls-files -z | xargs -0 "$PYTHON" tools/shells.py > "$logs/shells.log" 2>&1 || rc=$?
found=$(one_line < "$logs/shells.log")
if [ $rc = 0 ] && [ -n "$found" ]; then a=yes; else a=NO; fi
answer 9 "every tracked file of the folder that is a shell script has the line set -eu before its first command" $a "${found#shells: }"

# (10) to (13)
if [ $no != 0 ]; then
  for n in 10 11 12 13; do echo "gate: ($n) not asked: the make is not run, an answer above is NO"; done
elif [ -e _build ]; then
  answer 10 "make, from nothing, exits 0" NO "a _build is there: the make is not run"
  for n in 11 12 13; do echo "gate: ($n) not asked: the make is not run"; done
else
  start=$(date +%s); rc=0
  make -j1 CMI_ROOT="$build" > "$logs/make.log" 2>&1 || rc=$?
  took=$(( $(date +%s) - start ))
  if [ $rc = 0 ]; then a=yes; found="$took seconds"; else a=NO; found="exit status $rc after $took seconds: $(tail -1 "$logs/make.log" | cut -c1-200)"; fi
  answer 10 "make, from nothing, exits 0" $a "$found"
  found=$(git status --porcelain -- . | one_line)
  if [ -z "$found" ]; then a=yes; else a=NO; fi
  answer 11 "after the make, git status --porcelain of the folder is empty" $a "$found"
  disk=$(find . -type f | sed 's|^\./||' | of_dune)
  if on_disk extracted && on_disk runtime && [ "$disk" = dune ]; then a=yes; found=""
  else a=NO; found="not tracked, or not on the disk: $( { find extracted runtime -type f; git ls-files extracted runtime; } | LC_ALL=C sort | uniq -u | one_line); files of dune on the disk: ${disk:-none}"; fi
  answer 12 "after the make, the files on the disk under extracted/ and runtime/ are the tracked ones, and the folder's dune file is the only file of dune on the disk" $a "$found"
  found=$(git status --porcelain --ignored -- . | one_line)
  if [ "$found" = "!! $(git rev-parse --show-prefix)_build/" ]; then a=yes; found=""; else a=NO; found="it shows: ${found:-nothing}"; fi
  answer 13 "after the make, git status --porcelain --ignored of the folder shows _build/ and nothing else" $a "$found"
fi
if [ $no = 0 ]; then echo "gate: PASSED: every answer is yes"; else echo "gate: FAILED: the number of answers NO is $no"; fi
[ $no = 0 ]
