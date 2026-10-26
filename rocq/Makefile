# Check the Rocq models and proofs, and regenerate the extracted OCaml.
#
#   make          check every .v file, then run the extraction
#   make clean    remove everything generated
#
# The sources live in four directories, each a Rocq library:
#
#   rocq/                   OxcamlStdlib: models of OCaml's own types (int,
#                           Int64, lists, exceptions as options) and their
#                           extraction directives
#   backend/rocq/           OxcamlBackend: backend-wide definitions, such as
#                           the semantics of integer comparisons
#   backend/ssa/rocq/       OxcamlSsa: the SSA graph as the models see it
#                           (abstract blocks and values, with the few
#                           observations the passes make of them)
#   backend/ssa/loop/rocq/  OxcamlLoop: the loop passes and their extraction
#                           (Extract.v, one .ml per model); the wrappers
#                           around the extracted code are the modules of
#                           backend/ssa/loop/ itself
#
# The extracted files are run through ocamlformat so that they satisfy the
# repository's `make fmt` check like any other source under backend/ssa/.

ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/..)
ROCQ ?= rocq
OCAMLFORMAT ?= ocamlformat

STDLIB_DIR := $(ROOT)/rocq
BACKEND_DIR := $(ROOT)/backend/rocq
SSA_DIR := $(ROOT)/backend/ssa/rocq
LOOP_DIR := $(ROOT)/backend/ssa/loop/rocq

FLAGS := -Q $(STDLIB_DIR) OxcamlStdlib -Q $(BACKEND_DIR) OxcamlBackend \
  -Q $(SSA_DIR) OxcamlSsa -Q $(LOOP_DIR) OxcamlLoop

STDLIB := $(addprefix $(STDLIB_DIR)/, \
  OcamlOption.v ZTactics.v OcamlInt.v OcamlInt64.v OcamlList.v OcamlExtract.v)
BACKEND := $(addprefix $(BACKEND_DIR)/, \
  IntegerComparison.v IntegerComparisonExtract.v)
SSA := $(addprefix $(SSA_DIR)/, SsaModel.v SsaModelExtract.v)
LOOP := $(addprefix $(LOOP_DIR)/, \
  FourierMotzkin.v FourierMotzkinExtract.v LoopComparisons.v AffineExpr.v \
  AffineExprExtract.v NaturalLoop.v AffineSsa.v AffineSsaExtract.v \
  InductionVar.v InductionVarExtract.v LoopTermination.v DeadInductionVar.v \
  DeleteEmptyLoops.v)
EXTRACT := $(LOOP_DIR)/Extract.v

# The extraction writes one .ml and .mli per model into the loop directory;
# those of the SSA model are then moved next to their source.
SSA_EXTRACTED := $(addprefix $(SSA_DIR)/, SsaModel.ml SsaModel.mli)
LOOP_EXTRACTED := $(addprefix $(LOOP_DIR)/, \
  OcamlList.ml OcamlList.mli FourierMotzkin.ml FourierMotzkin.mli \
  LoopComparisons.ml LoopComparisons.mli AffineExpr.ml AffineExpr.mli \
  NaturalLoop.ml NaturalLoop.mli AffineSsa.ml AffineSsa.mli \
  InductionVar.ml InductionVar.mli LoopTermination.ml LoopTermination.mli \
  DeadInductionVar.ml DeadInductionVar.mli \
  DeleteEmptyLoops.ml DeleteEmptyLoops.mli)
EXTRACTED := $(SSA_EXTRACTED) $(LOOP_EXTRACTED)

SOURCES := $(STDLIB) $(BACKEND) $(SSA) $(LOOP) $(EXTRACT)
DEPS := $(STDLIB_DIR)/.rocqdeps.d

.PHONY: all clean

all: $(SOURCES:.v=.vo)

# Extract.v writes the .ml and .mli files into the loop directory. Separate
# extraction also writes an empty pair for every Rocq module whose contents
# are all mapped onto OCaml's own (OcamlInt, Uint63, ...); those are removed.
# It also puts the same `open M` lines at the top of a .ml and of its .mli;
# in the .mli only types can be referred to, so the open of a module that
# defines no types or submodules (OcamlList) is unused there, which warning
# 33 rejects. Such opens are removed from the .mli files.
$(EXTRACT:.v=.vo): $(EXTRACT)
	$(ROCQ) compile $(FLAGS) -output-directory $(LOOP_DIR) $<
	for f in $(LOOP_DIR)/*.ml $(LOOP_DIR)/*.mli; do \
	  grep -q '[^[:space:]]' $$f || rm -f $$f; done
	mv $(LOOP_DIR)/SsaModel.ml $(LOOP_DIR)/SsaModel.mli $(SSA_DIR)/
	@for f in $(LOOP_DIR)/*.ml $(LOOP_DIR)/*.mli; do \
	  case " $(LOOP_EXTRACTED) " in *" $$f "*) ;; *) \
	    echo "error: unexpected extracted file $$f: a model computes with" \
	      "something that has no OCaml realization (see OcamlExtract.v)"; \
	    exit 1;; \
	  esac; \
	done
	for f in $(LOOP_DIR)/*.mli $(SSA_DIR)/*.mli; do \
	  for m in `sed -n 's/^open \(.*\)$$/\1/p' $$f`; do \
	    cat $(LOOP_DIR)/$$m.mli $(SSA_DIR)/$$m.mli 2>/dev/null \
	      | grep -q -E '^ *(type|module) ' || \
	      { grep -v "^open $$m$$" $$f > $$f.tmp && mv $$f.tmp $$f; }; \
	  done; \
	done
	$(OCAMLFORMAT) -i $(EXTRACTED)

%.vo: %.v
	$(ROCQ) compile $(FLAGS) $<

# The dependencies between the .v files, computed by rocq dep.
$(DEPS): $(SOURCES)
	$(ROCQ) dep $(FLAGS) $(SOURCES) > $@

-include $(DEPS)

clean:
	rm -f $(DEPS) $(EXTRACTED)
	for d in $(STDLIB_DIR) $(BACKEND_DIR) $(SSA_DIR) $(LOOP_DIR); do \
	  rm -rf $$d/*.vo $$d/*.vos $$d/*.vok $$d/*.glob $$d/.*.aux \
	    $$d/.lia.cache $$d/.nia.cache $$d/.coq-native; \
	done
