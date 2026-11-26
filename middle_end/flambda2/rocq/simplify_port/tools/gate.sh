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
# OCAMLC, OCAMLFMT and PYTHON in the environment name other programs, as
# for make: the gate calls the ocamlformat that make calls. (Not
# OCAMLFORMAT: that variable of the environment is ocamlformat's own, for
# its options. The gate takes it out of its environment, as the Makefile
# does: the options are those of the .ocamlformat files alone.)
#
# It prints each thing that it asks with the answer, one line each
# ("gate: (N) ...: yes" or "... : NO", with what was found), and then PASSED
# or FAILED. Exit status 0 only if every answer is yes; 1 if one is NO; 2 if
# it was not given a build root, or if it may not write in the place of the
# logs (below): then it has asked nothing. Another status that is not 0: a
# command that the gate needs failed where no answer could say so, and the
# gate stopped there. One process at a time (make -j1).
#
# WHAT IT ASKS:
#  (1) before anything is made, the folder has only tracked files, none of
#      them changed, and no _build (git status --porcelain --ignored); and
#      no entry of the index for a file of the folder is marked
#      assume-unchanged or skip-worktree (git ls-files -v shows such an
#      entry with another letter than H). Git does not look at the file of
#      an entry that is marked so: git status would say nothing of a change
#      in it, here and in (11);
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
#  (8) every tracked .ml and .mli file of the folder for which ocamlformat
#      is not disabled is as ocamlformat leaves it (ocamlformat --check). A
#      file is left out only if ocamlformat --print-config ends well for it
#      and says disable=true; if that command fails for a file, or says
#      neither disable=true nor disable=false, the answer is NO;
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
#      has the tree as it was;
# (14) every tracked path of the folder is made only of the letters A to Z
#      and a to z, the digits, and the characters _ . / + - (no space, no
#      line break, no other character). IT IS ASKED SECOND, after (1): the
#      list that it reads is the list from which every thing after it takes
#      the names of the tracked files (below), and (2) to (7) and (12) read
#      that list by lines: they would cut in two a name with a line break.
#      (8) and (9) take each name whole all the same.
# The make is the long part (about 25 minutes). It is NOT RUN if an answer
# before it is NO, and the gate has then failed: (10) to (13) say "not
# asked".
#
# MAKE IS CALLED WITHOUT WHAT THE ENVIRONMENT SAYS TO EVERY MAKE: the
# variables MAKEFLAGS, MFLAGS, GNUMAKEFLAGS and MAKEFILES are taken out of
# the environment of the two calls, make list in (4) and the make of (10).
# With MAKEFLAGS=-i make goes on after a command that fails and exits 0;
# with -n it runs nothing and exits 0; a file of MAKEFILES is read before
# the Makefile. "make exits 0" would then not say that the commands of the
# Makefile ran and ended well. The other variables of the environment are
# left as they are: the Makefile takes the names of programs from it (ROCQ,
# OCAMLC, OCAMLFMT, PYTHON).
#
# WHERE A COMMAND THAT THE GATE ASKS FAILS, THE ANSWER IS NOT YES.
#
# Git is asked for the tracked files of the folder ONCE: git ls-files -z,
# into LOG_DIR/tracked.z, for (14), and its status is read. Every thing that
# needs the names of tracked files takes them from that list, and asks Git
# for no list of its own: (2), (3), (4), (5), (7), (8), (9) and (12). A list
# that Git wrote in part before it failed is so never taken for the whole.
#
# Each other question to Git is a command that stands alone, and its status
# is read: git status in (1), (11) and (13); git ls-files -v in (1); git
# rev-parse for the commit, for the path of the folder in (13), and in (3)
# for what the commit has at a path (there the status 1 is the answer "no
# such path", and a status above 1 is a failure, which the answer says). If
# one fails, an answer is NO (for the commit: the gate has failed, and says
# that the commit is not known). The directories of Git are asked for
# before the first thing: if that fails the gate stops with that status.
# git status is asked with --untracked-files=normal: a setting of Git that
# hides the files that are not tracked (status.showUntrackedFiles) does not
# hide them from the gate.
#
# The same holds for the other commands on whose output an answer is
# decided (find, ls, make, ocamlformat, and the tools that make the lists:
# sort, comm, cut, awk, sed, tr, cmp): each stands alone, with its output in
# a file of LOG_DIR/lists or in a variable, and its status is read, by the
# gate or by `set -e`, which stops the gate. AN ANSWER IS DECIDED ONLY ON
# WHAT SUCH A COMMAND WROTE. A pipe, in which the shell does not read the
# status of the first command, is used only for what is shown beside an
# answer (the function one_line).
#
# WHAT IT DOES NOT ASK: whether a range of commits changes a path outside
# the folder; who made the commits and how their subjects read; which words
# the texts use. The programs are named with their versions and not judged.
#
# THE PLACE OF THE LOGS is the second argument, LOG_DIR. It is made if it is
# not there. If it is not given, a new directory is made under the
# temporary directory (TMPDIR, or /tmp); the second line that the gate
# prints names it. It keeps decl.log, the decl/ that was made (decl/), the
# generator as it was compiled (declgen/), tracked.z (the tracked paths
# of the folder, each ended by a null byte), lists/ (the lists of names
# that the gate compares), list.log (what make list said), shells.log and
# make.log. What an
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
# them, nor be in one, nor hold one (what is removed first, LOG_DIR/decl
# or LOG_DIR/lists, could be it). Each path is compared as it is without its
# symbolic links,
# so a link to such a place is refused too. A temporary directory that is
# one of the four, or in one, is refused in the same way.
set -eu
if [ $# -lt 1 ] || [ ! -d "$1/middle_end/flambda2/simplify/.flambda2_simplify.objs/byte" ]; then
  echo "usage: tools/gate.sh BUILD_ROOT [LOG_DIR]"
  echo "  BUILD_ROOT: the _build/default of a dune build of the compiler from the sources of this tree"
  exit 2
fi
ROCQ=${ROCQ:-rocq}; OCAMLC=${OCAMLC:-ocamlc.opt}; PYTHON=${PYTHON:-python3}
OCAMLFMT=${OCAMLFMT:-ocamlformat}
unset OCAMLFORMAT
# physical PATH : the path without its symbolic links, whether or not
# something is there
physical() { "$PYTHON" -c 'import os, sys; print(os.path.realpath(sys.argv[1]))' "$1"; }
# within A B : is the path A the path B, or under it (two physical paths)
within() { local a=${1%/} b=${2%/}; case "$a/" in "$b/"*) return 0;; esac; return 1; }
build=$(physical "$1")
if [ $# -ge 2 ]; then given=yes; logs=$(physical "$2"); else given=no; logs=$(physical "${TMPDIR:-/tmp}"); fi
here=$(dirname "$0")
cd "$here/.."
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
rm -rf "$logs/decl" "$logs/declgen" "$logs/lists"
rm -f "$logs/decl.log" "$logs/decl.made" "$logs/decl.tracked" "$logs/tracked.z" "$logs/list.log" "$logs/shells.log" "$logs/make.log"
mkdir "$logs/lists"
lists=$logs/lists
no=0
nl='
'
# answer N WHAT yes|NO [FOUND] : one line; counts the answers NO
answer() {
  if [ "$3" = yes ]; then echo "gate: ($1) $2: yes${4:+ ($4)}"
  else echo "gate: ($1) $2: NO${4:+: $4}"; no=$((no+1)); fi
}
# one_line : the lines of the standard input on one line, the first 8. It is
# for what is shown: no answer is decided on what it writes.
one_line() { head -8 | tr '\n' ' ' | sed 's/ *$//'; }
# names FILE : the lines of a file on one line, the first 8; "none" if the
# file is empty. For what is shown.
names() { if [ -s "$1" ]; then one_line < "$1"; else echo none; fi; }
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
rc=0
commit=$(git rev-parse HEAD) || rc=$?
if [ $rc = 0 ]; then echo "gate: the commit of the tree is $commit; the folder is $(pwd)"
else echo "gate: the commit of the tree is NOT KNOWN: git rev-parse HEAD exits $rc; the folder is $(pwd)"; no=$((no+1)); fi
echo "gate: the build root is $build; the logs are in $logs"
version "$ROCQ" --version
version "$OCAMLC" -version
version ocamlfind ocamlopt -version
version "$OCAMLFMT" --version
version "$PYTHON" --version
version make --version
version git --version

# ask_status [--ignored] : asks git status --porcelain of the folder, the
# files that are not tracked with it whatever the settings of Git are. It
# sets status_rc, the status of git, and status_out, all that git wrote.
ask_status() {
  status_rc=0
  status_out=$(git status --porcelain --untracked-files=normal ${1:+"$1"} -- . 2>&1) || status_rc=$?
}
# status_shown : what the last ask_status found, for the line of the answer
status_shown() {
  if [ $status_rc != 0 ]; then echo "git status exits $status_rc, and says: $(printf '%s\n' "$status_out" | one_line)"
  else printf '%s\n' "$status_out" | one_line; fi
}

# (1)
ask_status --ignored
rc=0
entries=$(git ls-files -v -- . 2>&1) || rc=$?
nmarked=0; marked=""
while IFS= read -r line; do
  case "$line" in
  "H "*|"") ;;
  *) nmarked=$((nmarked+1)); if [ $nmarked -le 8 ]; then marked="$marked $line"; fi ;;
  esac
done <<< "$entries"
found=$(status_shown)
if [ $rc != 0 ]; then found="${found:+$found; }git ls-files -v exits $rc, and says:$marked"
elif [ $nmarked != 0 ]; then found="${found:+$found; }entries of the index that are marked (git ls-files -v), $nmarked:$marked"; fi
if [ $status_rc = 0 ] && [ -z "$status_out" ] && [ $rc = 0 ] && [ $nmarked = 0 ]; then a=yes; else a=NO; fi
answer 1 "before anything is made, the folder has only tracked files, none changed, none that the index tells Git not to look at, and no _build" $a "$found"

# (14). THE TRACKED FILES OF THE FOLDER ARE ASKED OF GIT HERE, ONCE: each
# name ended by a null byte, in tracked.z, and the status of git is read.
# Every thing below takes the names of tracked files from this list: (8) and
# (9) from tracked.z, each name whole; the others from lists/tracked, which
# has one name a line, sorted.
# plain NAME : is the name made only of the characters of (14)
plain() { local LC_ALL=C; case "$1" in ""|*[!A-Za-z0-9_./+-]*) return 1;; esac; return 0; }
rc=0
git ls-files -z > "$logs/tracked.z" || rc=$?
tr '\0' '\n' < "$logs/tracked.z" > "$lists/tracked.git"
LC_ALL=C sort "$lists/tracked.git" > "$lists/tracked"
all=0; bad=0; which=""
while IFS= read -r -d '' f; do
  all=$((all+1))
  if ! plain "$f"; then
    bad=$((bad+1))
    if [ $bad -le 4 ]; then which="$which $(printf '%q' "$f")"; fi
  fi
done < "$logs/tracked.z"
if [ $rc = 0 ] && [ $bad = 0 ] && [ $all -gt 0 ]; then a=yes; found="$all paths"
else
  a=NO; found="$bad of the $all paths, as the shell writes them:$which"
  if [ $rc != 0 ]; then found="git ls-files exits $rc; $found"; fi
fi
answer 14 "every tracked path of the folder is made only of letters, digits and the characters _ . / + -" $a "$found"

# (2)
rc=0
DECL_OUT="$logs/decl" DECLGEN_BUILD="$logs/declgen" tools/declgen/run.sh "$build" > "$logs/decl.log" 2>&1 || rc=$?
ls_rc=0
if [ -d "$logs/decl" ]; then ls "$logs/decl" > "$lists/decl.ls" || ls_rc=$?; else : > "$lists/decl.ls"; fi
LC_ALL=C sort "$lists/decl.ls" > "$lists/decl.made"
awk 'index($0, "decl/") == 1 && $0 != "decl/README.md" { print substr($0, 6) }' "$lists/tracked" > "$lists/decl.names"
LC_ALL=C sort "$lists/decl.names" > "$lists/decl.tracked"
LC_ALL=C comm -23 "$lists/decl.made" "$lists/decl.tracked" > "$lists/decl.only-made"
LC_ALL=C comm -13 "$lists/decl.made" "$lists/decl.tracked" > "$lists/decl.only-tree"
LC_ALL=C comm -12 "$lists/decl.made" "$lists/decl.tracked" > "$lists/decl.both"
differ=0; differing=""
while IFS= read -r f; do
  if ! cmp -s "$logs/decl/$f" "decl/$f"; then
    differ=$((differ+1))
    if [ $differ -le 6 ]; then differing="$differing $f"; fi
  fi
done < "$lists/decl.both"
found="$(wc -l < "$lists/decl.made") files made, $(wc -l < "$lists/decl.tracked") in the tree; $differ differ"
found="$found; only made: $(names "$lists/decl.only-made"); only in the tree: $(names "$lists/decl.only-tree")"
if [ $rc != 0 ]; then
  said=$(grep -A 2 '^declgen: ' "$logs/decl.log" | one_line) || true
  found="tools/declgen/run.sh exits $rc: ${said:-$(tail -1 "$logs/decl.log")}; $found"
fi
if [ $ls_rc != 0 ]; then found="ls exits $ls_rc; $found"; fi
if [ $differ != 0 ]; then found="$found; the first that differ:$differing"; fi
if [ $rc = 0 ] && [ $ls_rc = 0 ] && [ $differ = 0 ] && [ ! -s "$lists/decl.only-made" ] && [ ! -s "$lists/decl.only-tree" ] && [ -s "$lists/decl.made" ]; then a=yes; else a=NO; fi
answer 2 "decl/ made again from the build root is the decl/ of the tree, README.md apart" $a "$found"

# (3): for each file, what the commit has at the path that the file names.
# git rev-parse --verify -q exits 1 and writes nothing if the commit has no
# such path; another status is a failure of git, and is said.
n=0; bad=0; which=""; failed=0
while IFS= read -r f; do
  case "$f" in decl/*.v) ;; *) continue ;; esac
  n=$((n+1))
  rc=0
  blob=$(sed -n 's/^   (Git blob \([0-9a-f]\{40\}\)).*$/\1/p' "$f") || rc=$?
  path=$(awk '/^   \(Git blob [0-9a-f]+\)/ { sub(/^ */, "", prev); print prev; exit } { prev = $0 }' "$f") || rc=$?
  git_rc=0
  have=$(git rev-parse --verify -q "HEAD:$path" 2> /dev/null) || git_rc=$?
  if [ $git_rc -gt 1 ]; then failed=$((failed+1)); fi
  if [ $rc != 0 ] || [ $git_rc != 0 ] || [ -z "$blob" ] || [ "$blob" != "$have" ]; then
    bad=$((bad+1))
    if [ $bad -le 6 ]; then which="$which $f"; fi
  fi
done < "$lists/tracked"
if [ $bad = 0 ] && [ $n -gt 0 ]; then a=yes; found="$n files"
else
  a=NO; found="$bad of $n files:$which"
  if [ $failed != 0 ]; then found="$found; for $failed of them git rev-parse failed (a status above 1)"; fi
fi
answer 3 "each file that a file of decl/ says it follows has, in the commit, the text (Git blob) that the file of decl/ names" $a "$found"

# run_make ARGUMENT... : make, without what the environment says to every
# make
run_make() { env -u MAKEFLAGS -u MFLAGS -u GNUMAKEFLAGS -u MAKEFILES make "$@"; }

# (4) and (5)
# on_disk DIR : are the files on the disk under DIR the tracked ones. The two
# lists are made by commands that stand alone; if one fails, the answer is no.
on_disk() {
  find "$1" -type f > "$lists/$1.find" || return 1
  LC_ALL=C sort "$lists/$1.find" > "$lists/$1.disk" || return 1
  awk -v d="$1/" 'index($0, d) == 1' "$lists/tracked" > "$lists/$1.tracked" || return 1
  cmp -s "$lists/$1.disk" "$lists/$1.tracked"
}
# not_both DIR : the names that one of the two lists of on_disk has and the
# other does not. For what is shown.
not_both() { cat "$lists/$1.disk" "$lists/$1.tracked" | LC_ALL=C sort | uniq -u | one_line; }
rc=0
run_make -s list > "$logs/list.log" 2>&1 || rc=$?
cut -f3 "$logs/list.log" > "$lists/list.names"
LC_ALL=C sort "$lists/list.names" > "$lists/list.sorted"
awk 'index($0, "extracted/") == 1 && /\.ml$/' "$lists/tracked" > "$lists/extracted.ml"
others=$(awk 'index($0, "extracted/") == 1 && !/\.ml$/' "$lists/tracked")
if on_disk extracted; then same=yes; else same=no; fi
found="$(wc -l < "$lists/extracted.ml") tracked .ml files, $(wc -l < "$lists/list.sorted") lines of make list; the other tracked files: $(printf '%s\n' "${others:-none}" | one_line)"
if [ $rc != 0 ]; then found="make list exits $rc; $found"; fi
if [ $rc = 0 ] && cmp -s "$lists/list.sorted" "$lists/extracted.ml" && [ -s "$lists/extracted.ml" ] && [ "$others" = extracted/.ocamlformat ] && [ $same = yes ]; then a=yes
else a=NO; found="$found; on the disk and not tracked, or tracked and not on the disk: $(not_both extracted)"; fi
answer 4 "the tracked .ml files under extracted/ are those of make list, the one other file there is .ocamlformat, and the disk has the same files" $a "$found"
tracked=$(awk 'index($0, "runtime/") == 1 && /\.ml$/' "$lists/tracked")
others=$(awk 'index($0, "runtime/") == 1 && !/\.ml$/' "$lists/tracked")
if on_disk runtime; then same=yes; else same=no; fi
found="the tracked .ml files: $(printf '%s\n' "${tracked:-none}" | one_line); the other tracked files: $(printf '%s\n' "${others:-none}" | one_line)"
if [ "$tracked" = "runtime/port_abbreviations.ml${nl}runtime/port_monad.ml" ] && [ "$others" = runtime/.ocamlformat ] && [ $same = yes ]; then a=yes
else a=NO; found="$found; on the disk and not tracked, or tracked and not on the disk: $(not_both runtime)"; fi
answer 5 "the tracked .ml files under runtime/ are port_monad.ml and port_abbreviations.ml, the one other file there is .ocamlformat, and the disk has the same files" $a "$found"

# (6): a comment of dune is from a semicolon to the end of the line
stanzas=$(awk '{ sub(/;.*$/, ""); t = t " " $0 }
  END { gsub(/[ \t]+/, " ", t); sub(/^ /, "", t); sub(/ $/, "", t); gsub(/\( /, "(", t); gsub(/ \)/, ")", t); print t }' dune)
if [ "$stanzas" = "(include_subdirs no)" ]; then a=yes; found=""; else a=NO; found="it is: $(echo "$stanzas" | cut -c1-200)"; fi
answer 6 "the folder's dune file, its comments taken out, is the one stanza (include_subdirs no)" $a "$found"

# (7)
# of_dune FILE : the names in FILE, one a line, that dune or opam would read
of_dune() { awk '/^(dune|dune-project|dune-workspace)$/ || /\/(dune|dune-project|dune-workspace)$/ || /\.opam$/' "$1"; }
# all_disk : the files on the disk under the folder, one a line, in
# lists/all.disk; sets find_rc, the status of find
all_disk() {
  find_rc=0
  find . -type f > "$lists/all.find" || find_rc=$?
  sed 's|^\./||' "$lists/all.find" > "$lists/all.disk"
}
tracked=$(of_dune "$lists/tracked")
all_disk
disk=$(of_dune "$lists/all.disk")
if [ $find_rc = 0 ] && [ "$tracked" = dune ] && [ "$disk" = dune ]; then a=yes; found=""
else
  a=NO; found="tracked: $(printf '%s\n' "${tracked:-none}" | one_line); on the disk: $(printf '%s\n' "${disk:-none}" | one_line)"
  if [ $find_rc != 0 ]; then found="find exits $find_rc; $found"; fi
fi
answer 7 "no other file named dune, dune-project, dune-workspace or *.opam is in the folder, tracked or on the disk" $a "$found"

# (8): what ocamlformat --print-config says of a file is taken by a command
# that stands alone, and its status is read: a failure is not "disabled".
# The line disable=false or disable=true is looked for with the shell's own
# patterns ($nl is a line break).
all=0; on=0; off=0; bad=0; which=""; unsaid=0; unsaid_which=""
while IFS= read -r -d '' f; do
  case "$f" in *.ml|*.mli) ;; *) continue;; esac
  all=$((all+1))
  rc=0
  config=$("$OCAMLFMT" --print-config "$f" 2>&1 < /dev/null) || rc=$?
  if [ $rc != 0 ]; then config=""; fi
  case "$nl$config$nl" in
  *"${nl}disable=false$nl"*|*"${nl}disable=false "*)
    on=$((on+1))
    if ! "$OCAMLFMT" --check "$f" > /dev/null 2>&1 < /dev/null; then
      bad=$((bad+1))
      if [ $bad -le 6 ]; then which="$which $(printf '%q' "$f")"; fi
    fi ;;
  *"${nl}disable=true$nl"*|*"${nl}disable=true "*)
    off=$((off+1)) ;;
  *)
    unsaid=$((unsaid+1))
    if [ $unsaid -le 6 ]; then unsaid_which="$unsaid_which $(printf '%q' "$f")"; fi ;;
  esac
done < "$logs/tracked.z"
found="$on of the $all .ml and .mli files; ocamlformat is disabled for $off"
if [ $bad = 0 ] && [ $unsaid = 0 ] && [ $on -gt 0 ]; then a=yes
else
  a=NO
  if [ $bad != 0 ]; then found="$found; not as ocamlformat leaves them, $bad:$which"; fi
  if [ $unsaid != 0 ]; then found="$found; ocamlformat --print-config fails or does not say whether it is disabled, $unsaid:$unsaid_which"; fi
fi
answer 8 "every .ml and .mli file of the folder for which ocamlformat is not disabled is as ocamlformat leaves it" $a "$found"

# (9)
rc=0
xargs -0 "$PYTHON" tools/shells.py < "$logs/tracked.z" > "$logs/shells.log" 2>&1 || rc=$?
found=$(one_line < "$logs/shells.log")
if [ $rc = 0 ] && [ -s "$logs/shells.log" ]; then a=yes; else a=NO; fi
answer 9 "every tracked file of the folder that is a shell script has the line set -eu before its first command" $a "${found#shells: }"

# (10) to (13)
if [ $no != 0 ]; then
  for n in 10 11 12 13; do echo "gate: ($n) not asked: the make is not run, an answer above is NO"; done
elif [ -e _build ]; then
  answer 10 "make, from nothing, exits 0" NO "a _build is there: the make is not run"
  for n in 11 12 13; do echo "gate: ($n) not asked: the make is not run"; done
else
  start=$(date +%s); rc=0
  run_make -j1 CMI_ROOT="$build" > "$logs/make.log" 2>&1 || rc=$?
  took=$(( $(date +%s) - start ))
  if [ $rc = 0 ]; then a=yes; found="$took seconds"; else a=NO; found="exit status $rc after $took seconds: $(tail -1 "$logs/make.log" | cut -c1-200)"; fi
  answer 10 "make, from nothing, exits 0" $a "$found"
  ask_status
  if [ $status_rc = 0 ] && [ -z "$status_out" ]; then a=yes; else a=NO; fi
  answer 11 "after the make, git status --porcelain of the folder is empty" $a "$(status_shown)"
  all_disk
  disk=$(of_dune "$lists/all.disk")
  if on_disk extracted; then e=yes; else e=no; fi
  if on_disk runtime; then r=yes; else r=no; fi
  if [ $e = yes ] && [ $r = yes ] && [ $find_rc = 0 ] && [ "$disk" = dune ]; then a=yes; found=""
  else
    a=NO; found="not tracked, or not on the disk: $(not_both extracted) $(not_both runtime); files of dune on the disk: $(printf '%s\n' "${disk:-none}" | one_line)"
    if [ $find_rc != 0 ]; then found="find exits $find_rc; $found"; fi
  fi
  answer 12 "after the make, the files on the disk under extracted/ and runtime/ are the tracked ones, and the folder's dune file is the only file of dune on the disk" $a "$found"
  rc=0
  prefix=$(git rev-parse --show-prefix) || rc=$?
  ask_status --ignored
  if [ $rc = 0 ] && [ $status_rc = 0 ] && [ "$status_out" = "!! ${prefix}_build/" ]; then a=yes; found=""
  else
    a=NO; found=$(status_shown); found="it shows: ${found:-nothing}"
    if [ $rc != 0 ]; then found="git rev-parse --show-prefix exits $rc; $found"; fi
  fi
  answer 13 "after the make, git status --porcelain --ignored of the folder shows _build/ and nothing else" $a "$found"
fi
if [ $no = 0 ]; then echo "gate: PASSED: every answer is yes"; else echo "gate: FAILED: the number of answers NO is $no"; fi
[ $no = 0 ]
