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

# build.sh : compiles the generator of decl/ (one process) into
# simplify_port/_build/declgen/declgen; or into DIR/declgen, if
# DECLGEN_BUILD=DIR is in the environment (for a run that must make nothing
# in the folder; DIR is for this alone: the compiled files in it are
# removed first). It needs the compiler's own
# library (compiler-libs) of the OCaml that built the compiler whose
# interfaces are read. This file follows no file of the compiler.
set -eu
H=$(cd $(dirname $0) && pwd)
D=${DECLGEN_BUILD:-$H/../../_build/declgen}
mkdir -p $D
SRC="common.ml sigs.ml uses.ml tr.ml print.ml blob.ml src.ml decl_out.ml emit_types.ml walk.ml arities.ml donors.ml crs.ml declgen.ml"
for f in $SRC; do cp $H/$f $D/; done
cd $D && rm -f *.cm* *.o
ocamlfind ocamlopt -package compiler-libs.common,str -linkpkg $SRC -o declgen
