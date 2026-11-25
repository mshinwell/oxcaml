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

# run.sh BUILD_ROOT [UNIT ...] : makes decl/ again (run from simplify_port/).
# BUILD_ROOT is the _build/default of a build of the compiler from the
# sources of this tree. No commit is given: what is written depends on what
# is read, and the generator stops, and writes nothing, if the build
# compiled another text than the tree has (decl/README.md). With no UNIT,
# every file of Simplify is read; with units (Simplify_expr ...), only those
# files, and no question of crs.ml (that run does not make the decl/ of the
# tree). DECL_OUT=DIR in the environment: the files are written into DIR,
# which is made, and not into decl/ (to compare them with decl/).
# DECLGEN_BUILD=DIR: the generator is compiled in DIR (build.sh). One process
# at a time.
set -eu
B=$1; shift
H=$(cd $(dirname $0) && pwd)
O=$B/middle_end/flambda2/simplify/.flambda2_simplify.objs/byte
ROOT=$(cd $H/../../../../../.. && pwd)
OUT=${DECL_OUT:-decl}
D=${DECLGEN_BUILD:-$H/../../_build/declgen}
if [ $# = 0 ]; then
  CMTS=$(ls $O/flambda2_simplify__*.cmt | LC_ALL=C sort)
else
  CMTS=$(for u in "$@"; do echo $O/flambda2_simplify__$u.cmt; done)
  export DECLGEN_SOME_FILES=1
fi
$H/build.sh
mkdir -p $OUT
$D/declgen $B $ROOT $OUT $CMTS
