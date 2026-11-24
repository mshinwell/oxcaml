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

# The port of middle_end/flambda2/simplify/ to Rocq. Each ported file is
# compiled twice by Rocq, against the two implementations of the monad
# (monad/real: what the port means; monad/id: M A is A), and Rocq extracts
# the OCaml from the second build: direct style, by the extraction and its
# directives alone. ocamlformat formats it and OCaml checks its types against
# the compiler's compiled interfaces. This Makefile follows no file of the
# compiler. Read GUIDE.md.
#
#   make            everything below, one process at a time
#   make real       Rocq compiles everything against monad/real
#   make id         Rocq compiles everything against monad/id
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
OCAMLC ?= ocamlc.opt
OCAMLFORMAT ?= ocamlformat
PYTHON ?= python3
REPO_ROOT := ../../../..
CMI_ROOT ?= $(REPO_ROOT)/_build/default
SIMPLIFY := ../../simplify
B := _build

# The declarations of what the port calls: after the compiler's interfaces
# (decl/README.md).
DECL := $(patsubst %.v,%,$(sort $(wildcard decl/*.v)))

# THE TRANSCRIBED FILES. DIR/Foo_bar.v follows
# middle_end/flambda2/simplify/DIR/foo_bar.ml; [make list] prints the pairs.
SUBDIRS := env flow unboxing inlining lifting
PORTED := $(patsubst %.v,%,$(sort $(wildcard *.v \
  $(foreach d,$(SUBDIRS),$(d)/*.v))))

lc = $(shell echo '$(1)' | tr A-Z a-z)
reldir = $(patsubst ./%,%,$(dir $(1)))
donor = $(SIMPLIFY)/$(call reldir,$(1))$(call lc,$(notdir $(1))).ml
extracted = extracted/$(call reldir,$(1))$(call lc,$(notdir $(1))).ml
checked = $(B)/check/$(call reldir,$(1))$(call lc,$(notdir $(1))).status

SRC := $(addsuffix .v,$(DECL) $(PORTED))
REAL_V := $(B)/real/Port_monad.v $(B)/real/Kit_refuses.v $(addprefix $(B)/real/,$(SRC))
ID_V := $(B)/id/Port_monad.v $(addprefix $(B)/id/,$(SRC))
EXTRACTED := $(foreach p,$(PORTED),$(call extracted,$(p)))
CHECKED := $(foreach p,$(PORTED),$(call checked,$(p)))

.PHONY: all real id extract check table list clean
all: real id extract check table

real: $(REAL_V:.v=.vo)
id: $(ID_V:.v=.vo)
extract: $(EXTRACTED)
check: $(CHECKED)

list:
	@$(foreach p,$(PORTED),echo '$(p).v	$(call donor,$(p))	$(call extracted,$(p))';)

# ---- the two builds ---------------------------------------------------

# Each build is a copy of the sources beside its own Port_monad.v, so that
# the same text is compiled against each implementation.
$(B)/real/Port_monad.v: monad/real/Port_monad.v
	@mkdir -p $(dir $@) && cp $< $@
# What the types of the real monad must refuse.
$(B)/real/Kit_refuses.v: monad/real/Kit_refuses.v
	@mkdir -p $(dir $@) && cp $< $@
$(B)/id/Port_monad.v: monad/id/Port_monad.v
	@mkdir -p $(dir $@) && cp $< $@
$(B)/real/%.v: %.v
	@mkdir -p $(dir $@) && cp $< $@
$(B)/id/%.v: %.v
	@mkdir -p $(dir $@) && cp $< $@

$(B)/real/depend: $(REAL_V)
	@cd $(B)/real && $(ROCQ) dep -Q . SimplifyPort $(patsubst $(B)/real/%,%,$(REAL_V)) \
	  | sed -E 's#(^| )([^ /][^ ]*)#\1$(B)/real/\2#g' > depend
$(B)/id/depend: $(ID_V)
	@cd $(B)/id && $(ROCQ) dep -Q . SimplifyPort $(patsubst $(B)/id/%,%,$(ID_V)) \
	  | sed -E 's#(^| )([^ /][^ ]*)#\1$(B)/id/\2#g' > depend

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),list)
-include $(B)/real/depend
-include $(B)/id/depend
endif
endif

$(B)/real/%.vo: $(B)/real/%.v
	cd $(B)/real && $(ROCQ) compile -q -Q . SimplifyPort $*.v
$(B)/id/%.vo: $(B)/id/%.v
	cd $(B)/id && $(ROCQ) compile -q -Q . SimplifyPort $*.v

# ---- extraction and ocamlformat ---------------------------------------

# Rocq extracts the library DIR/Foo of the identity build. Flag 513: the
# erasure of what is logical (the fuel) and the inlining of a let that is
# used once (the temporaries of [let!]); every other optimisation of the
# extraction is off, and so is its automatic inlining. KeepSingleton: a
# record of one field stays a record (the payload of [Invalid { message }]).
$(B)/id/out/%.ml: $(B)/id/%.vo Makefile
	@mkdir -p $(dir $@) $(dir $(B)/id/extract/$*)
	@printf '%s\n' \
	  'From SimplifyPort Require Import Port_monad.' \
	  'Require SimplifyPort.$(subst /,.,$*).' \
	  'Set Extraction Output Directory "out/$(patsubst %/,%,$(call reldir,$*))".' \
	  'Set Extraction Flag 513.' \
	  'Unset Extraction AutoInline.' \
	  'Set Extraction KeepSingleton.' \
	  'Extraction Library $(notdir $*).' > $(B)/id/extract/$*_extract.v
	cd $(B)/id && $(ROCQ) compile -q -Q . SimplifyPort -w -extraction extract/$*_extract.v

# extracted/DIR/foo.ml: the header of the donor, a line that says where the
# file comes from, the OCaml text that the .v file carries verbatim, then
# what Rocq extracted, unchanged; formatted by ocamlformat with the options
# of extracted/.ocamlformat (a copy of middle_end/flambda2/.ocamlformat, so
# that an editor or dune formats these files in the same way). Before that,
# tools/lint.py: each temporary of [let!] is used once.
define PORT_RULES
$(call extracted,$(1)): $(B)/id/out/$(1).ml $(1).v $(call donor,$(1)) tools/assemble.sh tools/lint.py extracted/.ocamlformat
	@mkdir -p $$(dir $$@)
	$(PYTHON) tools/lint.py $(1).v
	tools/assemble.sh $(1).v $(call donor,$(1)) $(B)/id/out/$(1).ml > $$@
	$(OCAMLFORMAT) --inplace $$@

$(call checked,$(1)): $(call extracted,$(1)) $(B)/check/port_monad.cmi tools/check.sh
	@mkdir -p $$(dir $$@)
	@CMI_ROOT='$(CMI_ROOT)' OCAMLC='$(OCAMLC)' RUNTIME='$(B)/check' tools/check.sh $(call extracted,$(1)) $(SIMPLIFY) $$@
endef
$(foreach p,$(PORTED),$(eval $(call PORT_RULES,$(p))))

# The OCaml that the extracted files call (runtime/port_monad.ml).
$(B)/check/port_monad.cmi: runtime/port_monad.ml tools/check.sh
	@mkdir -p $(B)/check
	@CMI_ROOT='$(CMI_ROOT)' OCAMLC='$(OCAMLC)' RUNTIME='$(B)/check' tools/check.sh --runtime runtime/port_monad.ml

# ---- the table --------------------------------------------------------

table: PROGRESS.md
PROGRESS.md: real id $(EXTRACTED) $(CHECKED) tools/progress.sh
	tools/progress.sh $(SIMPLIFY) $(B) > $@

clean:
	rm -rf $(B)
