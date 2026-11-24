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
#
# The file is compiled as the module Foo__port with the -open flags of
# middle_end/flambda2/simplify/dune, so every name in it is the compiler's
# own, and with -nolabels: the Rocq text has no labels, and OCaml's classic
# mode ignores the labels of the interfaces.
#   strict : Foo__port has the whole interface foo.mli of the compiler.
#   overlay: the compiler's module, with the extracted definitions in the
#            place of its own, has the compiler's interface. (For a file
#            that is not whole yet: what is not ported stays the compiler's.)
#   alone  : the compiler's file has no interface; the file compiles.
# The status file holds one of these words, or "skipped" without CMI_ROOT.
f=$1; simplify=$2; status=$3
rel=${f#extracted/}; dir=$(dirname "$rel"); base=$(basename "$rel" .ml)
out=$(dirname "$status")/$base.d
rm -rf "$out"; mkdir -p "$out"
S=$CMI_ROOT/middle_end/flambda2
if [ ! -d "$S/simplify/.flambda2_simplify.objs/byte" ]; then
  echo "check: no compiled interfaces under CMI_ROOT=$CMI_ROOT: $f not checked"
  echo skipped > "$status"; exit 0
fi
INC="-I $CMI_ROOT/.ocamlcommon.objs/byte -I $CMI_ROOT/.oxcaml_common.objs/byte"
INC="$INC -I $CMI_ROOT/.ocamlfrontend.objs/byte"
INC="$INC -I $CMI_ROOT/.ocamlbytecomp.objs/byte -I $CMI_ROOT/.ocamloptcomp.objs/byte"
for d in algorithms bound_identifiers classic_mode_types cmx compare datalog \
  from_lambda identifiers import kinds lattices nominal numbers parser reaper \
  simplify simplify_shared term_basics terms to_cmm to_jsir types ui; do
  [ -d "$S/$d/.flambda2_$d.objs/byte" ] && INC="$INC -I $S/$d/.flambda2_$d.objs/byte"
done
OPENS="-open Flambda2_algorithms -open Flambda2_bound_identifiers"
OPENS="$OPENS -open Flambda2_cmx -open Flambda2_identifiers -open Flambda2_kinds"
OPENS="$OPENS -open Flambda2_lattices -open Flambda2_numbers -open Flambda2_nominal"
OPENS="$OPENS -open Flambda2_term_basics -open Flambda2_terms"
OPENS="$OPENS -open Flambda2_simplify_shared -open Flambda2_types -open Flambda2_ui"
OPENS="$OPENS -open Flambda2_simplify"
CC="$OCAMLC -c -nolabels -w -a $INC $OPENS -I $out"
mli=$simplify/$dir/$base.mli
cp "$f" "$out/${base}__port.ml"
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
