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
# BUILD_ROOT is the _build/default of a build of the compiler at the commit
# of the sources. With no UNIT, every file of Simplify is read; with units
# (Simplify_expr ...), only those files, and no question of crs.ml (that
# run does not make the decl/ of the tree). One process at a time.
set -e
B=$1; shift
H=$(cd $(dirname $0) && pwd)
O=$B/middle_end/flambda2/simplify/.flambda2_simplify.objs/byte
ROOT=$(cd $H/../../../../../.. && pwd)
COMMIT=${COMMIT:-ecc5c0d968c892b4312065caef0f19ffffa042a9}
if [ $# = 0 ]; then
  CMTS=$(ls $O/flambda2_simplify__*.cmt | LC_ALL=C sort)
else
  CMTS=$(for u in "$@"; do echo $O/flambda2_simplify__$u.cmt; done)
  export DECLGEN_SOME_FILES=1
fi
$H/build.sh
mkdir -p decl
$H/../../_build/declgen/declgen $B $ROOT decl $COMMIT $CMTS
