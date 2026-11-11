# Check the Rocq models and proofs, and regenerate the extracted OxCaml.
#
#   make          check every .v file, then run the extraction
#   make assumptions  print global assumptions and declaration types, and
#                 check the axioms against the trust ledger (TRUST-LEDGER.md)
#   make claims   check that every statement a Spec file binds is proved
#   make review   typeset what a reviewer reads as rocq/review.pdf
#   make clean    remove everything generated
#
# The sources live in six directories, each a Rocq library:
#
#   rocq/                   OxCamlStdlib: models of OxCaml's own types (int,
#                           Int64, lists, exceptions as options), generic
#                           integer arithmetic, and their extraction
#                           directives; see HACKING.md there
#   backend/rocq/           OxCamlBackend: backend-wide definitions, such as
#                           the semantics of integer comparisons and the
#                           operations of the backend's instructions
#   backend/ssa/rocq/       OxCamlSsa: the SSA graph as the models see it
#                           (abstract blocks and values, with the few
#                           observations the passes make of them), and the
#                           properties of terminators, uses and dominance
#                           that any pass may need
#   backend/ssa/loop/rocq/  OxCamlLoop: the loop analyses and their
#                           extraction (Extract.v, one .ml per model); the
#                           passes using them are backend/ssa/loop/
#                           delete_empty_loops.ml and bounds_check_elim.ml
#   middle_end/flambda2/rocq/  OxCamlFlambda2: the terms of Flambda 2 and
#                           their semantics, with rewrites proved against
#                           it; extracted for tests only (FlambdaExtract.v)
#   middle_end/flambda2/types/rocq/  OxCamlFlambda2Types: Flambda types and
#                           typing environments, and refinement relative to
#                           a typing environment; extracted likewise
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
FLAMBDA2_DIR := $(ROOT)/middle_end/flambda2/rocq
FLAMBDA2_TYPES_DIR := $(ROOT)/middle_end/flambda2/types/rocq

FLAGS := -Q $(STDLIB_DIR) OxCamlStdlib -Q $(BACKEND_DIR) OxCamlBackend \
  -Q $(SSA_DIR) OxCamlSsa -Q $(LOOP_DIR) OxCamlLoop \
  -Q $(FLAMBDA2_DIR) OxCamlFlambda2 \
  -Q $(FLAMBDA2_TYPES_DIR) OxCamlFlambda2Types

STDLIB := $(addprefix $(STDLIB_DIR)/, \
  OxCamlLogic.v OxCamlOption.v ZTactics.v OxCamlInt.v OxCamlIntProofs.v \
  OxCamlInt64.v OxCamlInt64Proofs.v OxCamlList.v OxCamlListProofs.v \
  IntArith.v IntArithProofs.v OxCamlExtract.v IntArithExtract.v)
BACKEND := $(addprefix $(BACKEND_DIR)/, \
  IntegerComparison.v IntegerComparisonProofs.v IntegerComparisonExtract.v \
  Operation.v OperationExtract.v)
SSA := $(addprefix $(SSA_DIR)/, \
  SsaModel.v SsaModelExtract.v SsaGraphSpec.v SsaGraph.v SsaGraphProofs.v \
  SsaDominanceSpec.v SsaDominance.v SsaDominanceProofs.v SsaSemanticsSpec.v \
  SsaSemantics.v SsaSemanticsProofs.v SsaExecutionSpec.v \
  SsaExecutionProofs.v SsaLivenessSpec.v SsaLivenessProofs.v \
  SsaProgressSpec.v SsaProgressProofs.v SsaContextSpec.v SsaContextProofs.v)
LOOP := $(addprefix $(LOOP_DIR)/, \
  FourierMotzkin.v FourierMotzkinProofs.v FourierMotzkinExtract.v \
  LoopComparisons.v LoopComparisonsProofs.v AffineExpr.v AffineExprProofs.v \
  AffineExprExtract.v NaturalLoop.v NaturalLoopProofs.v AffineSsa.v \
  AffineSsaProofs.v AffineSsaExtract.v InductionVar.v InductionVarProofs.v \
  InductionVarExtract.v LoopTermination.v LoopTerminationProofs.v \
  DeadInductionVar.v DeadInductionVarProofs.v DeleteEmptyLoopsSpec.v \
  DeleteEmptyLoops.v DeleteEmptyLoopsProofs.v InductionRange.v \
  InductionRangeProofs.v BoundsCheckElim.v BoundsCheckElimProofs.v \
  LoopExecutionProofs.v LoopInvariantExecutionProofs.v \
  LoopCounterExecutionProofs.v LoopLiveOutProofs.v LoopEligibilitySpec.v \
  LoopEligibilityProofs.v LoopValueSnapshotProofs.v \
  LoopGuardExecutionProofs.v LoopRangeExecutionProofs.v \
  InductionRangeExecutionProofs.v BoundsCheckExecutionSpec.v \
  BoundsCheckExecutionProofs.v)
EXTRACT := $(LOOP_DIR)/Extract.v
# The files of the two Flambda 2 libraries: one to a line, in alphabetical
# order, so that branches that each add a file merge. The order means
# nothing: make takes the dependencies from rocq dep, and the review
# document puts the files in dependency order itself (review-pdf.pl).
FLAMBDA2 := $(addprefix $(FLAMBDA2_DIR)/, \
  FlambdaAlphaFreshProofs.v \
  FlambdaAlphaFreshSpec.v \
  FlambdaAlphaGroupProofs.v \
  FlambdaAlphaGroupSpec.v \
  FlambdaAlphaProofs.v \
  FlambdaAlphaSpec.v \
  FlambdaApplyProofs.v \
  FlambdaApplySpec.v \
  FlambdaBindersProofs.v \
  FlambdaBindersSpec.v \
  FlambdaBlockLoadProofs.v \
  FlambdaBlockLoadSpec.v \
  FlambdaCanonicalFreeNamesProofs.v \
  FlambdaCanonicalFreeNamesSpec.v \
  FlambdaClosuresProofs.v \
  FlambdaClosuresSpec.v \
  FlambdaCompareAlphaProofs.v \
  FlambdaCompareAlphaSpec.v \
  FlambdaCompareConverseProofs.v \
  FlambdaCompareConverseSpec.v \
  FlambdaCompareProofs.v \
  FlambdaCompareSpec.v \
  FlambdaContextProofs.v \
  FlambdaContextSpec.v \
  FlambdaContextWhereProofs.v \
  FlambdaContextWhereSpec.v \
  FlambdaControlFlowProofs.v \
  FlambdaControlFlowSpec.v \
  FlambdaEquivarianceProofs.v \
  FlambdaEquivarianceSpec.v \
  FlambdaFreeNamesProofs.v \
  FlambdaFreeNamesSpec.v \
  FlambdaFreshAbstractionProofs.v \
  FlambdaFreshAbstractionSpec.v \
  FlambdaFreshBindersProofs.v \
  FlambdaFreshBindersSpec.v \
  FlambdaFreshQuantifierProofs.v \
  FlambdaFreshQuantifierSpec.v \
  FlambdaIdentitiesProofs.v \
  FlambdaIdentitiesSpec.v \
  FlambdaInlineFreshProofs.v \
  FlambdaInlineFreshSpec.v \
  FlambdaKindModel.v \
  FlambdaLiftProofs.v \
  FlambdaLiftSpec.v \
  FlambdaMapProofs.v \
  FlambdaMapSpec.v \
  FlambdaModel.v \
  FlambdaMyClosureProofs.v \
  FlambdaMyClosureSpec.v \
  FlambdaNameAbstractionProofs.v \
  FlambdaNameAbstractionSpec.v \
  FlambdaNominalInstancesProofs.v \
  FlambdaNominalInstancesSpec.v \
  FlambdaNominalProofs.v \
  FlambdaNominalSpec.v \
  FlambdaNormaliseProofs.v \
  FlambdaNormaliseSpec.v \
  FlambdaPrimitiveModel.v \
  FlambdaPrimitiveProofs.v \
  FlambdaPrimitiveSpec.v \
  FlambdaRangeProofs.v \
  FlambdaRangeSpec.v \
  FlambdaScopeProofs.v \
  FlambdaScopeSpec.v \
  FlambdaSemanticsProofs.v \
  FlambdaSemanticsSpec.v \
  FlambdaSimulationProofs.v \
  FlambdaStateSupportProofs.v \
  FlambdaStateSupportSpec.v \
  FlambdaStaticProofs.v \
  FlambdaStaticSpec.v \
  FlambdaTrapProofs.v \
  FlambdaTrapSpec.v \
  FlambdaUnboxProofs.v \
  FlambdaUnboxSpec.v \
  FlambdaUnusedContsProofs.v \
  FlambdaUnusedContsSpec.v \
  FlambdaUnusedStaticsProofs.v \
  FlambdaUnusedStaticsSpec.v \
  FlambdaValidateProofs.v \
  FlambdaValidateSpec.v \
  FlambdaValidatorEquivarianceProofs.v \
  FlambdaValidatorEquivarianceSpec.v \
  FlambdaValueProofs.v \
  FlambdaValueSpec.v \
  FlambdaWellFormedProofs.v \
  FlambdaWellFormedSpec.v \
  FlambdaWellKindedProofs.v \
  FlambdaWellKindedSpec.v \
)
FLAMBDA2_EXTRACT := $(FLAMBDA2_DIR)/FlambdaExtract.v
FLAMBDA2_EXTRACTED_DIR := $(ROOT)/middle_end/flambda2/tests/semantics/extracted
FLAMBDA2_TYPES := $(addprefix $(FLAMBDA2_TYPES_DIR)/, \
  FlambdaAliasesProofs.v \
  FlambdaAliasesSpec.v \
  FlambdaBindingTime.v \
  FlambdaEnvAliases.v \
  FlambdaEnvAliasesFollowProofs.v \
  FlambdaEnvAliasesFollowSpec.v \
  FlambdaEnvAliasesInvariantProofs.v \
  FlambdaEnvAliasesInvariantSpec.v \
  FlambdaEnvAliasesProofs.v \
  FlambdaEnvAliasesRenamingProofs.v \
  FlambdaEnvAliasesRenamingSpec.v \
  FlambdaEnvAliasesSetProofs.v \
  FlambdaEnvAliasesSetSpec.v \
  FlambdaEnvAliasesSpec.v \
  FlambdaExpandHead.v \
  FlambdaExpandHeadProofs.v \
  FlambdaExpandHeadSpec.v \
  FlambdaJoinEnv.v \
  FlambdaJoinEnvProofs.v \
  FlambdaJoinEnvSpec.v \
  FlambdaJoinProofs.v \
  FlambdaJoinSpec.v \
  FlambdaJoinStateProofs.v \
  FlambdaJoinStateSpec.v \
  FlambdaJoinTypes.v \
  FlambdaJoinTypesExamplesProofs.v \
  FlambdaJoinTypesExamplesSpec.v \
  FlambdaJoinTypesKeepsProofs.v \
  FlambdaJoinTypesKeepsSpec.v \
  FlambdaJoinTypesProofs.v \
  FlambdaJoinTypesSpec.v \
  FlambdaJoinTypesWithEnvProofs.v \
  FlambdaJoinTypesWithEnvSpec.v \
  FlambdaMeet.v \
  FlambdaMeetEnv.v \
  FlambdaMeetEnvProofs.v \
  FlambdaMeetEnvSpec.v \
  FlambdaMeetExamplesProofs.v \
  FlambdaMeetExamplesSpec.v \
  FlambdaMeetGrammar.v \
  FlambdaMeetProofs.v \
  FlambdaMeetScopesProofs.v \
  FlambdaMeetScopesSpec.v \
  FlambdaMeetSpec.v \
  FlambdaMeetStepsProofs.v \
  FlambdaMeetStepsSpec.v \
  FlambdaProvers.v \
  FlambdaProversExamplesProofs.v \
  FlambdaProversExamplesSpec.v \
  FlambdaProversProofs.v \
  FlambdaProversSpec.v \
  FlambdaProversStandIn.v \
  FlambdaReify.v \
  FlambdaReifyProofs.v \
  FlambdaReifySpec.v \
  FlambdaTypeAccessProofs.v \
  FlambdaTypeAccessSpec.v \
  FlambdaTypeAliasKindsProofs.v \
  FlambdaTypeAliasKindsSpec.v \
  FlambdaTypeCreatorsProofs.v \
  FlambdaTypeCreatorsSpec.v \
  FlambdaTypeEqualProofs.v \
  FlambdaTypeEqualSpec.v \
  FlambdaTypeGrammar.v \
  FlambdaTypeGrammarProofs.v \
  FlambdaTypeMeaningBoolProofs.v \
  FlambdaTypeMeaningBoolSpec.v \
  FlambdaTypeMeaningProofs.v \
  FlambdaTypeMeaningSpec.v \
  FlambdaTypeNominalProofs.v \
  FlambdaTypeNominalSpec.v \
  FlambdaTypeProject.v \
  FlambdaTypeRenameProofs.v \
  FlambdaTypeRenameSpec.v \
  FlambdaTypeWellFormedProofs.v \
  FlambdaTypeWellFormedSpec.v \
  FlambdaTypesProofs.v \
  FlambdaTypesSpec.v \
  FlambdaTypingEnv.v \
  FlambdaTypingEnvExamplesProofs.v \
  FlambdaTypingEnvExamplesSpec.v \
  FlambdaTypingEnvExtension.v \
  FlambdaTypingEnvExtensionProofs.v \
  FlambdaTypingEnvExtensionSpec.v \
  FlambdaTypingEnvInvariantProofs.v \
  FlambdaTypingEnvInvariantSpec.v \
  FlambdaTypingEnvKindedProofs.v \
  FlambdaTypingEnvKindedSpec.v \
  FlambdaTypingEnvOperationsProofs.v \
  FlambdaTypingEnvOperationsSpec.v \
  FlambdaTypingEnvProofs.v \
  FlambdaTypingEnvRangeProofs.v \
  FlambdaTypingEnvRangeSpec.v \
  FlambdaTypingEnvRefinementProofs.v \
  FlambdaTypingEnvRefinementSpec.v \
  FlambdaTypingEnvSpec.v \
)

# The extraction writes one .ml and .mli per model into the loop directory;
# those of the SSA models are then moved next to their sources. Those of the
# rocq/ models that are not mapped onto OxCaml's own functions (OxCamlList,
# IntArith) stay in the loop directory.
SSA_MODULES := SsaModel SsaGraphSpec SsaGraph SsaDominance SsaSemanticsSpec \
  SsaSemantics
SSA_EXTRACTED := $(addprefix $(SSA_DIR)/, \
  $(foreach m, $(SSA_MODULES), $(m).ml $(m).mli))
LOOP_EXTRACTED := $(addprefix $(LOOP_DIR)/, \
  OxCamlList.ml OxCamlList.mli IntArith.ml IntArith.mli \
  FourierMotzkin.ml FourierMotzkin.mli \
  LoopComparisons.ml LoopComparisons.mli AffineExpr.ml AffineExpr.mli \
  NaturalLoop.ml NaturalLoop.mli AffineSsa.ml AffineSsa.mli \
  InductionVar.ml InductionVar.mli LoopTermination.ml LoopTermination.mli \
  DeadInductionVar.ml DeadInductionVar.mli \
  DeleteEmptyLoops.ml DeleteEmptyLoops.mli \
  InductionRange.ml InductionRange.mli \
  BoundsCheckElim.ml BoundsCheckElim.mli)
EXTRACTED := $(SSA_EXTRACTED) $(LOOP_EXTRACTED)

SOURCES := $(STDLIB) $(BACKEND) $(SSA) $(LOOP) $(EXTRACT) $(FLAMBDA2) \
  $(FLAMBDA2_TYPES) $(FLAMBDA2_EXTRACT)
MODULES := $(patsubst $(STDLIB_DIR)/%.v,OxCamlStdlib.%,$(STDLIB)) \
  $(patsubst $(BACKEND_DIR)/%.v,OxCamlBackend.%,$(BACKEND)) \
  $(patsubst $(SSA_DIR)/%.v,OxCamlSsa.%,$(SSA)) \
  $(patsubst $(LOOP_DIR)/%.v,OxCamlLoop.%,$(LOOP) $(EXTRACT)) \
  $(patsubst $(FLAMBDA2_DIR)/%.v,OxCamlFlambda2.%,$(FLAMBDA2) \
    $(FLAMBDA2_EXTRACT)) \
  $(patsubst $(FLAMBDA2_TYPES_DIR)/%.v,OxCamlFlambda2Types.%,$(FLAMBDA2_TYPES))
DEPS := $(STDLIB_DIR)/.rocqdeps.d

.PHONY: all assumptions claims review clean

all: $(SOURCES:.v=.vo) claims

# The review document, rocq/review.pdf: ROCQ-REVIEW-GUIDE.md, in parts, with
# every reviewed .v file (definitions and statements; the implementation and
# Proofs files are left out), the extraction directives and the axioms the
# statements rest on, typeset by rocq doc and LuaLaTeX (HACKING.md, "The
# review document").
review: $(SOURCES:.v=.vo)
	perl $(STDLIB_DIR)/review-pdf.pl $(STDLIB_DIR)/_review \
	  $(STDLIB_DIR)/review.pdf $(STDLIB) $(BACKEND) $(SSA) $(LOOP) $(EXTRACT) \
	  $(FLAMBDA2) $(FLAMBDA2_TYPES) $(FLAMBDA2_EXTRACT)

# Every statement a Spec file binds as a proposition ([Definition X_statement
# : Prop]) must be proved as the theorem [X] of the matching Proofs module
# (HACKING.md, "The layout of a model"). Each is checked by defining a
# constant of the statement's type whose body is the theorem; on success the
# claims checked are listed. The constant is named after the Spec file and
# the statement, so that two Spec files may each have a statement of one name.
# A statement is found by its first line, so [Definition X_statement : Prop]
# must be on one line: a Spec file with a [Definition] of a name ending in
# [_statement] that is written otherwise is an error, as such a statement
# would not be checked.
SPECS := $(patsubst %,OxCamlSsa:%,$(filter %Spec.v,$(SSA))) \
  $(patsubst %,OxCamlLoop:%,$(filter %Spec.v,$(LOOP))) \
  $(patsubst %,OxCamlFlambda2:%,$(filter %Spec.v,$(FLAMBDA2))) \
  $(patsubst %,OxCamlFlambda2Types:%,$(filter %Spec.v,$(FLAMBDA2_TYPES)))

claims: $(SOURCES:.v=.vo)
	@set -eu; \
	  claims_dir=$$(mktemp -d); \
	  trap 'rm -rf "$$claims_dir"' 0; \
	  : > "$$claims_dir/list"; \
	  for entry in $(SPECS); do \
	    lib=$${entry%%:*}; spec=$${entry#*:}; \
	    module=$$(basename $$spec .v); proofs=$${module%Spec}Proofs; \
	    if grep -n '^Definition [^ ]*_statement\( \|$$\)' $$spec \
	        | grep -v '^[0-9]*:Definition [A-Za-z0-9_]*_statement : Prop' \
	        >&2; then \
	      echo "$$spec: a statement that make claims would not check;" \
	        "write [Definition X_statement : Prop] on one line" >&2; \
	      exit 1; \
	    fi; \
	    for claim in $$(sed -n \
	        's/^Definition \([A-Za-z0-9_]*\)_statement : Prop.*/\1/p' $$spec); \
	    do \
	      printf 'From %s Require %s %s.\n' $$lib $$module $$proofs; \
	      printf 'Definition %s_%s_claim : %s.%s_statement := %s.%s.\n' \
	        $$module $$claim $$module $$claim $$proofs $$claim; \
	      printf '%s.%s proves %s.%s_statement\n' \
	        $$proofs $$claim $$module $$claim >> "$$claims_dir/list"; \
	    done; \
	  done > "$$claims_dir/Claims.v"; \
	  $(ROCQ) repl -q -batch $(FLAGS) -l "$$claims_dir/Claims.v"; \
	  cat "$$claims_dir/list"

# The checker reports global assumptions, not theorem premises. Constant
# types also expose Section arguments and contract fields,
# including declarations inside nested modules.
#
# The axioms are checked against the trust ledger (TRUST-LEDGER.md), and the
# target fails if they differ: an axiom that Rocq reports must be listed
# there, and an axiom listed there must be reported. An axiom is listed by a
# list item beginning with its fully qualified name between backquotes.
# Then every statement of the Flambda 2 libraries (the theorems that claims
# checks) must depend only on axioms of the ledger's section "Flambda 2".
# Print Assumptions names an axiom by the shortest name that is not
# ambiguous, so one is taken to be listed if a listed name ends with it.
LEDGER := $(STDLIB_DIR)/TRUST-LEDGER.md
FLAMBDA2_SPECS := $(patsubst %,OxCamlFlambda2:%,$(filter %Spec.v,$(FLAMBDA2))) \
  $(patsubst %,OxCamlFlambda2Types:%,$(filter %Spec.v,$(FLAMBDA2_TYPES)))

assumptions: all
	@printf '%s\n' '=== Global assumptions (including dependencies) ==='
	@set -eu; \
	  ledger_dir=$$(mktemp -d); \
	  trap 'rm -rf "$$ledger_dir"' 0; \
	  cd "$$ledger_dir"; \
	  $(ROCQ) check -silent -o $(FLAGS) $(MODULES) > check 2>&1 \
	    || { cat check; exit 1; }; \
	  cat check; \
	  sed -n '/^\* Axioms:/,/^\* /p' check \
	    | sed -n 's/^    \([^ ][^ ]*\)$$/\1/p' | LC_ALL=C sort -u > reported; \
	  sed -n 's/^- `\([A-Za-z0-9_.'"'"']*\)`.*/\1/p' $(LEDGER) \
	    | LC_ALL=C sort -u > listed; \
	  LC_ALL=C comm -23 reported listed > unlisted; \
	  LC_ALL=C comm -13 reported listed > stale; \
	  printf '\n%s\n' '=== The axioms against the trust ledger ==='; \
	  if [ -s unlisted ]; then \
	    echo "error: axioms that $(LEDGER) does not list:" >&2; \
	    sed 's/^/  /' unlisted >&2; \
	  fi; \
	  if [ -s stale ]; then \
	    echo "error: axioms that $(LEDGER) lists and Rocq does not report:" \
	      >&2; \
	    sed 's/^/  /' stale >&2; \
	  fi; \
	  [ ! -s unlisted ] && [ ! -s stale ] || exit 1; \
	  echo "The $$(wc -l < reported | tr -d ' ') axioms reported are those of" \
	    "the trust ledger."; \
	  for entry in $(FLAMBDA2_SPECS); do \
	    lib=$${entry%%:*}; spec=$${entry#*:}; \
	    module=$$(basename $$spec .v); proofs=$${module%Spec}Proofs; \
	    for claim in $$(sed -n \
	        's/^Definition \([A-Za-z0-9_]*\)_statement : Prop.*/\1/p' $$spec); \
	    do \
	      printf 'From %s Require %s.\nPrint Assumptions %s.%s.\n' \
	        $$lib $$proofs $$proofs $$claim; \
	    done; \
	  done > Statements.v; \
	  $(ROCQ) repl -q -batch $(FLAGS) -l Statements.v > statements 2>&1 \
	    || { cat statements; exit 1; }; \
	  sed -n 's/^\([A-Za-z_][A-Za-z0-9_.'"'"']*\)\( :.*\)\{0,1\}$$/\1/p' \
	    statements | grep -v '^Axioms$$' | LC_ALL=C sort -u > used; \
	  sed -n '/^## Flambda 2$$/,/^## /p' $(LEDGER) \
	    | sed -n 's/^- `\([A-Za-z0-9_.'"'"']*\)`.*/\1/p' > flambda2; \
	  : > foreign; \
	  while read -r axiom; do \
	    grep -q -x -e "$$axiom" -e ".*\.$$axiom" flambda2 \
	      || echo "$$axiom" >> foreign; \
	  done < used; \
	  if [ -s foreign ]; then \
	    echo "error: statements of the Flambda 2 libraries depend on axioms" \
	      "that are not in the section \"Flambda 2\" of $(LEDGER):" >&2; \
	    sed 's/^/  /' foreign >&2; \
	    exit 1; \
	  fi; \
	  echo "The statements of the Flambda 2 libraries depend on" \
	    "$$(wc -l < used | tr -d ' ') of the $$(wc -l < flambda2 | tr -d ' ')" \
	    "axioms of the ledger's section \"Flambda 2\", and on no other."
	@printf '\n%s\n' '=== Declaration types and contract fields ===' \
	  'Section hypotheses appear as arguments in these types.' \
	  'This section includes proved theorems, not just assumptions.'
	@set -eu; \
	  audit_dir=$$(mktemp -d); \
	  trap 'rm -rf "$$audit_dir"' 0; \
	  { printf '%s\n' 'Set Printing Width 78.' \
	      'Set Printing Depth 1000000.'; \
	    for module in $(MODULES); do \
	      printf 'Require %s.\nPrint Namespace %s.\n' "$$module" "$$module"; \
	    done; \
	  } > "$$audit_dir/Assumptions.v"; \
	  $(ROCQ) repl -q -batch $(FLAGS) -l "$$audit_dir/Assumptions.v"

# Extract.v writes the .ml and .mli files into the loop directory. Separate
# extraction also writes an empty pair for every Rocq module whose contents
# are all mapped onto OxCaml's own (OxCamlInt, Uint63, ...); those are removed.
# It also puts the same `open M` lines at the top of a .ml and of its .mli;
# in the .mli only types can be referred to, so the open of a module that
# defines no types or submodules (OxCamlList) is unused there, which warning
# 33 rejects. Such opens are removed from the .mli files.
$(EXTRACT:.v=.vo): $(EXTRACT)
	$(ROCQ) compile $(FLAGS) -output-directory $(LOOP_DIR) $<
	for f in $(LOOP_DIR)/*.ml $(LOOP_DIR)/*.mli; do \
	  grep -q '[^[:space:]]' $$f || rm -f $$f; done
	mv $(foreach m, $(SSA_MODULES), $(LOOP_DIR)/$(m).ml $(LOOP_DIR)/$(m).mli) \
	  $(SSA_DIR)/
	@for f in $(LOOP_DIR)/*.ml $(LOOP_DIR)/*.mli; do \
	  case " $(LOOP_EXTRACTED) " in *" $$f "*) ;; *) \
	    echo "error: unexpected extracted file $$f: a model computes with" \
	      "something that has no OxCaml realization (see OxCamlExtract.v)"; \
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

# FlambdaExtract.v writes the machine of the Flambda 2 semantics as OCaml
# modules into the directory of the test tool that runs it
# (middle_end/flambda2/tests/semantics/extracted/); nothing there is written
# by hand but the dune file.
$(FLAMBDA2_EXTRACT:.v=.vo): $(FLAMBDA2_EXTRACT)
	cd $(FLAMBDA2_EXTRACTED_DIR) && $(ROCQ) compile $(FLAGS) $<
	$(OCAMLFORMAT) -i $(FLAMBDA2_EXTRACTED_DIR)/*.ml \
	  $(FLAMBDA2_EXTRACTED_DIR)/*.mli

%.vo: %.v
	$(ROCQ) compile $(FLAGS) $<

# The dependencies between the .v files, computed by rocq dep. They are
# written to another file, which is renamed when rocq dep has succeeded:
# a run that fails (rocq is not on the path, say) must not leave an empty
# file that is newer than the sources, as later builds would take it for
# the dependencies and rebuild nothing.
$(DEPS): $(SOURCES)
	$(ROCQ) dep $(FLAGS) $(SOURCES) > $@.tmp || { rm -f $@.tmp; exit 1; }
	mv $@.tmp $@

-include $(DEPS)

clean:
	rm -f $(DEPS) $(DEPS).tmp $(EXTRACTED) $(STDLIB_DIR)/review.pdf
	rm -rf $(STDLIB_DIR)/_review
	for d in $(STDLIB_DIR) $(BACKEND_DIR) $(SSA_DIR) $(LOOP_DIR) \
	    $(FLAMBDA2_DIR) $(FLAMBDA2_TYPES_DIR); do \
	  rm -rf $$d/*.vo $$d/*.vos $$d/*.vok $$d/*.glob $$d/.*.aux \
	    $$d/.lia.cache $$d/.nia.cache $$d/.coq-native; \
	done
