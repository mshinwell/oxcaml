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

# check.sh extracted/DIR/foo.ml SIMPLIFY_DIR STATUS_FILE : the types of one
# extracted file, against the compiler's compiled interfaces under CMI_ROOT
# (the _build/default of a dune build). It follows no file of the compiler.
# What it READS of the compiler: the compiled interfaces under CMI_ROOT, and
# the interface SIMPLIFY_DIR/DIR/foo.mli, which it compares with dune's copy
# under CMI_ROOT and of which it compiles a copy in its scratch output (the
# modes strict and --instr). It writes nothing of them into the folder.
# check.sh --runtime runtime/FILE.ml : compiles one file of the runtime of the
# port (port_monad.ml, port_abbreviations.ml) into the directory RUNTIME.
# check.sh --instr FILE.ml SIMPLIFY_DIR OUT_FILE : compiles the extracted file
# in the same way and writes to OUT_FILE the bytecode instructions that ocamlc
# makes of it (-dinstr); for tools/samecode.sh. Two kinds of places are made
# blank in them, and nothing else: the place (file, line, character) of a
# failed assertion, where the instructions build it and raise Assert_failure
# at once, and the text of a `__LOC__`; both only if they name this very
# file. OUT_FILE.places gets three counts: the assertions, the `__LOC__`s,
# and the times that the file's name stands elsewhere in the instructions
# (left as it is). Without compiled interfaces this mode FAILS.
# check.sh --runtime-instr runtime/FILE.ml OUT_FILE : the same for a file of
# the runtime.
#
# The file is compiled as the module Foo__port with the -open flags of
# middle_end/flambda2/simplify/dune, so every name in it is the compiler's
# own, and with -nolabels: the Rocq text has no labels, and OCaml's classic
# mode ignores the labels of the interfaces (and takes the arguments in the
# order of the interface).
#   strict : Foo__port has the whole interface foo.mli of the compiler.
#   overlay: the compiler's module, with the extracted definitions in the
#            place of its own, has the compiler's interface. (For a file
#            that is not whole yet: what is not ported stays the compiler's.)
#   alone  : the compiler's file has no interface; the file compiles.
# The status file holds one of these words, or "skipped" without CMI_ROOT.
set -eu
# What the environment may leave out is empty: without CMI_ROOT there are no
# compiled interfaces (below); RUNTIME is not read by --runtime-instr.
CMI_ROOT=${CMI_ROOT:-}; OCAMLC=${OCAMLC:-}; RUNTIME=${RUNTIME:-}
S=$CMI_ROOT/middle_end/flambda2
INC="-I $CMI_ROOT/.ocamlcommon.objs/byte -I $CMI_ROOT/.oxcaml_common.objs/byte"
INC="$INC -I $CMI_ROOT/.ocamlfrontend.objs/byte"
INC="$INC -I $CMI_ROOT/.ocamlbytecomp.objs/byte -I $CMI_ROOT/.ocamloptcomp.objs/byte"
INC="$INC -I $CMI_ROOT/backend/debug/dwarf/dwarf_flags/.dwarf_flags.objs/byte"
INC="$INC -I $S/numbers/floats/.flambda2_floats.objs/byte"
for d in algorithms bound_identifiers classic_mode_types cmx compare datalog \
  from_lambda identifiers import kinds lattices nominal numbers parser reaper \
  simplify simplify_shared term_basics terms to_cmm to_jsir types ui; do
  if [ -d "$S/$d/.flambda2_$d.objs/byte" ]; then
    INC="$INC -I $S/$d/.flambda2_$d.objs/byte"
  fi
done
have_cmi() { [ -d "$S/simplify/.flambda2_simplify.objs/byte" ]; }
# blank_places FILE RAW OUT : RAW (the output of -dinstr for FILE, by the name
# that ocamlc was given) with the two kinds of places made blank; OUT.places.
# What stands in their stead is no constant that ocamlc can print (it has no
# quotes and no brackets), so it cannot be taken for one of the file's own;
# the mark # that ocamlc puts before the string of a `__LOC__` is kept.
blank_places() {
  P="$1" perl -0ne '
    my $p = quotemeta($ENV{P});
    my $a = s/\bconst\s+\[0:\s+"$p"\s+\d+\s+\d+\]
              (?=\s+push\s+getglobal\ Assert_failure\/\d+!
                 \s+makeblock\ 2,\ 0\s+raise\b)
             /const <THE-PLACE-OF-AN-ASSERTION>/gx;
    my $l = s/\bconst\s+(\#?)"File\ \\"$p\\",\ line\ \d+,\ characters\ \d+-\d+"
             /const $1<THE-TEXT-OF-A-LOC>/gx;
    my $r = () = /$p/g;
    print; printf STDERR "%d %d %d\n", $a || 0, $l || 0, $r;' \
    "$2" > "$3" 2> "$3.places"
}
if [ "${1:-}" = --runtime-instr ]; then
  r=$(basename "$2" .ml); status=$3; out=$(dirname "$status")/$r.d
  rm -rf "$out"; mkdir -p "$out"
  if ! have_cmi; then
    echo "check: no compiled interfaces under CMI_ROOT=$CMI_ROOT: no instructions of $2"; exit 1
  fi
  cp "$2" "$out/$r.ml"
  $OCAMLC -c -w -a $INC -dinstr "$out/$r.ml" > "$out/instr.raw" 2>&1 \
    || { head -20 "$out/instr.raw"; exit 1; }
  blank_places "$out/$r.ml" "$out/instr.raw" "$status"
  exit 0
fi
if [ "${1:-}" = --runtime ]; then
  mkdir -p "$RUNTIME"
  r=$(basename "$2" .ml)
  if ! have_cmi; then
    echo "check: no compiled interfaces under CMI_ROOT=$CMI_ROOT: the runtime is not compiled"
    : > "$RUNTIME/$r.cmi"; exit 0
  fi
  cp "$2" "$RUNTIME/$r.ml"
  $OCAMLC -c -w -a $INC "$RUNTIME/$r.ml" || exit 1
  echo "check: $2: compiled"; exit 0
fi
mode=check
if [ "${1:-}" = --instr ]; then mode=instr; shift; fi
f=$1; simplify=$2; status=$3
rel=${f#*extracted/}; dir=$(dirname "$rel"); base=$(basename "$rel" .ml)
out=$(dirname "$status")/$base.d
rm -rf "$out"; mkdir -p "$out"
if ! have_cmi; then
  if [ $mode = instr ]; then
    echo "check: no compiled interfaces under CMI_ROOT=$CMI_ROOT: no instructions of $f"; exit 1
  fi
  echo "check: no compiled interfaces under CMI_ROOT=$CMI_ROOT: $f not checked"
  echo skipped > "$status"; exit 0
fi
OPENS="-open Flambda2_algorithms -open Flambda2_bound_identifiers"
OPENS="$OPENS -open Flambda2_cmx -open Flambda2_identifiers -open Flambda2_kinds"
OPENS="$OPENS -open Flambda2_lattices -open Flambda2_numbers -open Flambda2_nominal"
OPENS="$OPENS -open Flambda2_term_basics -open Flambda2_terms"
OPENS="$OPENS -open Flambda2_simplify_shared -open Flambda2_types -open Flambda2_ui"
OPENS="$OPENS -open Flambda2_simplify"
CC="$OCAMLC -c -nolabels -w -a $INC -I $RUNTIME $OPENS -I $out"
mli=$simplify/$dir/$base.mli
# The compiled interfaces must be those of this source tree: dune keeps a
# copy of each source under CMI_ROOT.
built=$S/simplify/$dir/$base.mli
if [ -e "$mli" ] && [ -e "$built" ] && ! cmp -s "$mli" "$built"; then
  echo FAILED > "$status"
  echo "check: $f: $built is not $mli: CMI_ROOT is of another source tree"
  exit 1
fi
cp "$f" "$out/${base}__port.ml"
if [ $mode = instr ]; then
  # The instructions say no name of a variable and no spelling of a module:
  # two extracted files that differ only in how names are written give the
  # same text here, but for the places that blank_places makes blank.
  if [ -e "$mli" ]; then
    cp "$mli" "$out/${base}__port.mli"
    $CC "$out/${base}__port.mli" > "$out/instr.log" 2>&1 || { cat "$out/instr.log"; exit 1; }
  fi
  $CC -dinstr "$out/${base}__port.ml" > "$out/instr.raw" 2>&1 || { head -20 "$out/instr.raw"; exit 1; }
  blank_places "$out/${base}__port.ml" "$out/instr.raw" "$status"
  exit 0
fi
if [ -e "$mli" ]; then
  cp "$mli" "$out/${base}__port.mli"
  if $CC "$out/${base}__port.mli" > "$out/strict.log" 2>&1 \
     && $CC "$out/${base}__port.ml" >> "$out/strict.log" 2>&1; then
    echo strict > "$status"; echo "check: $f: strict"; exit 0
  fi
  rm -f "$out/${base}__port.mli" "$out"/*.cm*
fi
if $CC "$out/${base}__port.ml" > "$out/overlay.log" 2>&1; then
  if [ ! -e "$mli" ]; then
    echo alone > "$status"; echo "check: $f: alone"; exit 0
  fi
  m=${base^}
  printf '%s\n' \
    "module Check : module type of struct include Flambda2_simplify.$m end = struct" \
    "  include Flambda2_simplify.$m" \
    "  include ${m}__port" \
    "end" > "$out/check_$base.ml"
  if $CC "$out/check_$base.ml" >> "$out/overlay.log" 2>&1; then
    echo overlay > "$status"; echo "check: $f: overlay"; exit 0
  fi
fi
echo FAILED > "$status"
echo "check: $f: THE TYPES DO NOT CHECK ($out/overlay.log):"
head -40 "$out/overlay.log"
exit 1
