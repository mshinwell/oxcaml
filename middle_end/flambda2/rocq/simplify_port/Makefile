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

# The port of middle_end/flambda2/simplify/ to Rocq: Rocq compiles each
# file, extracts it, tools/unmonad writes the extraction in direct style,
# ocamlformat formats it, and OCaml checks its types against the compiler's
# compiled interfaces. This Makefile follows no file of the compiler. Read
# GUIDE.md.
#
#   make            everything below, one process at a time
#   make tooltest   the tests of tools/unmonad
#   make rocq       Rocq compiles the kit, decl/ and the ported files
#   make extract    extracted/DIR/foo.ml for every ported file
#   make check      the types of every extracted file
#   make table      PROGRESS.md
#   make list       the ported files and their donors
#   make clean
#
# CMI_ROOT is the _build/default of a dune build of this repository (the
# compiled interfaces that the check reads). Without it the check says so
# and does nothing.

SHELL := /bin/bash
.SECONDARY:
.DELETE_ON_ERROR:

ROCQ ?= rocq
OCAMLFIND ?= ocamlfind
OCAMLC ?= ocamlc.opt
OCAMLFORMAT ?= ocamlformat
REPO_ROOT := ../../../..
CMI_ROOT ?= $(REPO_ROOT)/_build/default
SIMPLIFY := ../../simplify
B := _build
ROCQFLAGS := -q -Q . SimplifyPort

# The kit: Rocq files that follow no file of the compiler.
KIT := Port_monad

# The declarations of what the port calls: generated from the compiler's
# interfaces (decl/README.md).
DECL := $(patsubst %.v,%,$(sort $(wildcard decl/*.v)))

# THE TRANSCRIBED FILES. DIR/Foo_bar.v follows
# middle_end/flambda2/simplify/DIR/foo_bar.ml; [make list] prints the pairs.
# A .v file in these directories that is not of the kit must have its donor.
SUBDIRS := env flow unboxing inlining lifting
PORTED := $(filter-out $(KIT),$(patsubst %.v,%,$(sort $(wildcard *.v \
  $(foreach d,$(SUBDIRS),$(d)/*.v)))))

lc = $(shell echo '$(1)' | tr A-Z a-z)
donor = $(SIMPLIFY)/$(patsubst ./%,%,$(dir $(1)))$(call lc,$(notdir $(1))).ml
extracted = extracted/$(patsubst ./%,%,$(dir $(1)))$(call lc,$(notdir $(1))).ml
checked = $(B)/check/$(patsubst ./%,%,$(dir $(1)))$(call lc,$(notdir $(1))).status

VFILES := $(addsuffix .v,$(KIT) $(DECL) $(PORTED))
VOFILES := $(VFILES:.v=.vo)
EXTRACTED := $(foreach p,$(PORTED),$(call extracted,$(p)))
CHECKED := $(foreach p,$(PORTED),$(call checked,$(p)))
UNMONAD := $(B)/tools/unmonad

.PHONY: all tooltest rocq extract check table list clean
all: tooltest rocq extract check table

rocq: $(VOFILES)
extract: $(EXTRACTED)
check: $(CHECKED)

list:
	@$(foreach p,$(PORTED),echo '$(p).v	$(call donor,$(p))	$(call extracted,$(p))';)

# ---- Rocq -------------------------------------------------------------

$(B)/depend: $(VFILES)
	@mkdir -p $(B)
	@$(ROCQ) dep -Q . SimplifyPort $(VFILES) > $@

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),list)
-include $(B)/depend
endif
endif

%.vo: %.v
	$(ROCQ) compile $(ROCQFLAGS) $<

# ---- the tool ---------------------------------------------------------

$(UNMONAD): tools/unmonad.ml
	@mkdir -p $(B)/tools
	cp tools/unmonad.ml $(B)/tools/unmonad.ml
	cd $(B)/tools && $(OCAMLFIND) ocamlopt -package compiler-libs.common \
	  -linkpkg -w -a unmonad.ml -o unmonad

# The tool refuses each file tools/test/reject_*.ml and writes
# tools/test/accept_*.expected for accept_*.ml (tools/test/README.md).
tooltest: $(UNMONAD)
	@for f in tools/test/reject_*.ml; do \
	  if $(UNMONAD) $$f -o /dev/null 2> /dev/null; then \
	    echo "tooltest: $$f WAS NOT REFUSED"; exit 1; fi; done
	@for f in tools/test/accept_*.ml; do \
	  $(UNMONAD) $$f -o $(B)/tools/accept.out \
	  && cmp -s $(B)/tools/accept.out $${f%.ml}.expected \
	  || { echo "tooltest: $$f: not the expected output"; exit 1; }; done
	@echo "tooltest: passed"

# ---- extraction, the removal of the monad, ocamlformat ----------------

# Rocq extracts the library DIR/Foo to $(B)/raw/DIR/Foo.ml. The optimisations
# of the extraction are off; what makes the result faithful is not that but
# the discipline that tools/unmonad checks (GUIDE.md, section 3).
$(B)/raw/%.ml: %.vo
	@mkdir -p $(dir $@) $(dir $(B)/extract/$*)
	@printf '%s\n' \
	  'From SimplifyPort Require Import Port_monad.' \
	  'Require SimplifyPort.$(subst /,.,$*).' \
	  'Set Extraction Output Directory "$(patsubst %/,%,$(dir $@))".' \
	  'Unset Extraction Optimize.' \
	  'Unset Extraction AutoInline.' \
	  'Extraction Library $(notdir $*).' > $(B)/extract/$*_extract.v
	$(ROCQ) compile $(ROCQFLAGS) -w -extraction $(B)/extract/$*_extract.v

# The tool also gives the variables the names of the .v file again and,
# for a file that opens Simplify_import, writes the module paths with the
# short names of simplify_import.ml, as the compiler's files do.
$(B)/direct/%.ml: $(B)/raw/%.ml %.v $(UNMONAD) $(SIMPLIFY)/simplify_import.ml
	@mkdir -p $(dir $@)
	$(UNMONAD) $< -names $*.v \
	  $$(grep -q '^open! Simplify_import' $*.v \
	     && echo -aliases $(SIMPLIFY)/simplify_import.ml) -o $@

# extracted/DIR/foo.ml: the header of the donor, a line that says where the
# file comes from, the OCaml text that the .v file carries verbatim, then
# the direct-style code; formatted by ocamlformat with the options of
# extracted/.ocamlformat (a copy of middle_end/flambda2/.ocamlformat, so
# that an editor or dune formats these files in the same way).
define PORT_RULES
$(call extracted,$(1)): $(B)/direct/$(1).ml $(1).v $(call donor,$(1)) tools/assemble.sh extracted/.ocamlformat
	@mkdir -p $$(dir $$@)
	tools/assemble.sh $(1).v $(call donor,$(1)) $(B)/direct/$(1).ml > $$@
	$(OCAMLFORMAT) --inplace $$@

$(call checked,$(1)): $(call extracted,$(1)) tools/check.sh
	@mkdir -p $$(dir $$@)
	@CMI_ROOT='$(CMI_ROOT)' OCAMLC='$(OCAMLC)' tools/check.sh $(call extracted,$(1)) $(SIMPLIFY) $$(basename $$@)
endef
$(foreach p,$(PORTED),$(eval $(call PORT_RULES,$(p))))

# ---- the table --------------------------------------------------------

table: PROGRESS.md
PROGRESS.md: $(VOFILES) $(EXTRACTED) $(CHECKED) tools/progress.sh
	tools/progress.sh $(SIMPLIFY) $(B) > $@

clean:
	rm -rf $(B)
	find . -name '*.vo' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \
	  -o -name '.*.aux' | xargs rm -f
