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
#   make real       Rocq compiles everything against monad/real: the
#                   declarations, the ported files, the laws of the kit
#                   (monad/real/Kit_laws.v), the contracts (contracts/) and
#                   the first lemmas (proofs/)
#   make id         Rocq compiles everything against monad/id
#   make extract    extracted/DIR/foo.ml for every ported file
#   make check      the types of every extracted file, make given, make
#                   lines, make follows, make exceptions and make papp
#   make given      the OCaml text that the ported files give, against the
#                   compiler's files
#   make lines      the notes of lines of the ported files, against the
#                   compiler's files
#   make exceptions what a declared exception may carry
#   make papp       the partial applications of functions of the ported
#                   files, against the definitions in extracted/
#   make shells     every shell script of the folder has `set -eu` before
#                   its first command
#   make follows    the first comment of each ported file names its donor
#                   and the text of the donor that the tree has
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

# The tools of Python write no compiled copy of themselves beside the
# sources (tools/__pycache__): what make leaves in the folder is under
# $(B)/, or is a tracked file that it makes again. tools/gate.sh asks it.
export PYTHONDONTWRITEBYTECODE := 1

# The declarations of what the port calls: after the compiler's interfaces
# (decl/README.md).
DECL := $(patsubst %.v,%,$(sort $(wildcard decl/*.v)))

# The abbreviations of modules that a file of the compiler makes itself
# ([module DE = Downwards_env]), as a library that the ported file imports
# (GUIDE.md, section 7).
ABBREV := $(patsubst %.v,%,$(sort $(wildcard abbrev/*/*.v)))

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

# The contracts of the parameters (contracts/README.md) and the first
# lemmas about the ported files (proofs/README.md). Files of the real build
# only: the identity build never compiles them, and nothing of them is
# extracted.
CONTRACTS := $(patsubst %.v,%,$(sort $(wildcard contracts/*.v \
  contracts/ported/*.v contracts/ported/*/*.v)))
PROOFS := $(patsubst %.v,%,$(sort $(wildcard proofs/*.v proofs/*/*.v)))

SRC := $(addsuffix .v,$(DECL) $(ABBREV) $(PORTED))
REAL_V := $(B)/real/Port_monad.v $(B)/real/Kit_refuses.v \
  $(B)/real/Kit_laws.v $(addprefix $(B)/real/,$(SRC)) \
  $(addprefix $(B)/real/,$(addsuffix .v,$(CONTRACTS) $(PROOFS)))
ID_V := $(B)/id/Port_monad.v $(addprefix $(B)/id/,$(SRC))
EXTRACTED := $(foreach p,$(PORTED),$(call extracted,$(p)))
CHECKED := $(foreach p,$(PORTED),$(call checked,$(p)))

.PHONY: all real id extract check given lines follows shells exceptions papp table comments list clean
all: shells real id extract check table comments

real: $(REAL_V:.v=.vo)
id: $(ID_V:.v=.vo)
extract: $(EXTRACTED)
check: shells given lines follows exceptions $(CHECKED) papp

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
# The laws of the real monad, and the rules for a proof about a ported
# function.
$(B)/real/Kit_laws.v: monad/real/Kit_laws.v
	@mkdir -p $(dir $@) && cp $< $@
$(B)/id/Port_monad.v: monad/id/Port_monad.v
	@mkdir -p $(dir $@) && cp $< $@
$(B)/real/%.v: %.v
	@mkdir -p $(dir $@) && cp $< $@
$(B)/id/%.v: %.v
	@mkdir -p $(dir $@) && cp $< $@

# What each file depends on, as Rocq says it, with the directory of the
# build before each name. A FAILURE OF [rocq dep] STOPS MAKE. So the
# recipe is three commands, each run only if the one before it ended well,
# and not a pipe (a pipe ends well when [rocq dep] fails and sed does
# not); the list has the name depend only when it is whole (until then it
# is depend.rocq and depend.tmp); and the lists are taken by [include],
# not [-include] (with [-include] make goes on without a list that could
# not be made, and says nothing). The seven targets that need no list
# (clean, list, given, lines, shells, exceptions, follows), each asked
# alone, do not ask for one.
$(B)/real/depend: $(REAL_V)
	@cd $(B)/real && $(ROCQ) dep -Q . SimplifyPort $(patsubst $(B)/real/%,%,$(REAL_V)) > depend.rocq \
	  && sed -E 's#(^| )([^ /][^ ]*)#\1$(B)/real/\2#g' depend.rocq > depend.tmp \
	  && mv depend.tmp depend
$(B)/id/depend: $(ID_V)
	@cd $(B)/id && $(ROCQ) dep -Q . SimplifyPort $(patsubst $(B)/id/%,%,$(ID_V)) > depend.rocq \
	  && sed -E 's#(^| )([^ /][^ ]*)#\1$(B)/id/\2#g' depend.rocq > depend.tmp \
	  && mv depend.tmp depend

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),list)
ifneq ($(MAKECMDGOALS),given)
ifneq ($(MAKECMDGOALS),lines)
ifneq ($(MAKECMDGOALS),shells)
ifneq ($(MAKECMDGOALS),exceptions)
ifneq ($(MAKECMDGOALS),follows)
include $(B)/real/depend
include $(B)/id/depend
endif
endif
endif
endif
endif
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
# Before the extraction, tools/aliases.py gives the directives by which a
# name that the file reaches through an abbreviation of a module is printed
# with that abbreviation (GUIDE.md, section 7).
# When the declarations of the file's own module (decl/Foo.v) are loaded
# too, through what the file requires, Rocq names its output Foo0.ml: the
# rule gives it the name Foo.ml.
$(B)/id/out/%.ml: $(B)/id/%.vo Makefile tools/aliases.py
	@mkdir -p $(dir $@) $(dir $(B)/id/extract/$*)
	@rm -f $@ $(B)/id/out/$*0.ml
	@printf '%s\n' \
	  'From SimplifyPort Require Import Port_monad.' \
	  'Require SimplifyPort.$(subst /,.,$*).' > $(B)/id/extract/$*_extract.v
	@$(PYTHON) tools/aliases.py $*.v decl abbrev >> $(B)/id/extract/$*_extract.v
	@printf '%s\n' \
	  'Set Extraction Output Directory "out/$(patsubst %/,%,$(call reldir,$*))".' \
	  'Set Extraction Flag 513.' \
	  'Unset Extraction AutoInline.' \
	  'Set Extraction KeepSingleton.' \
	  'Extraction Library $(notdir $*).' >> $(B)/id/extract/$*_extract.v
	cd $(B)/id && $(ROCQ) compile -q -Q . SimplifyPort -w -extraction extract/$*_extract.v
	@[ -e $@ ] || mv $(B)/id/out/$*0.ml $@

# extracted/DIR/foo.ml: the header of the donor, a line that says where the
# file comes from, the OCaml text that the .v file carries verbatim, then
# what Rocq extracted, unchanged; formatted by ocamlformat with the options
# of extracted/.ocamlformat (a copy of middle_end/flambda2/.ocamlformat, so
# that an editor or dune formats these files in the same way). Before that,
# tools/lint.py: each temporary of [let!] is used once; and its other
# checks, the last of which (tools/papp.py) reads decl/ARITIES.tsv.
define PORT_RULES
$(call extracted,$(1)): $(B)/id/out/$(1).ml $(1).v $(call donor,$(1)) tools/assemble.sh tools/lint.py tools/papp.py decl/ARITIES.tsv extracted/.ocamlformat
	@mkdir -p $$(dir $$@)
	$(PYTHON) tools/lint.py $(1).v
	tools/assemble.sh $(1).v $(call donor,$(1)) $(B)/id/out/$(1).ml > $$@
	$(OCAMLFORMAT) --inplace $$@

$(call checked,$(1)): $(call extracted,$(1)) $(B)/check/port_monad.cmi $(B)/check/port_abbreviations.cmi tools/check.sh
	@mkdir -p $$(dir $$@)
	@CMI_ROOT='$(CMI_ROOT)' OCAMLC='$(OCAMLC)' RUNTIME='$(B)/check' tools/check.sh $(call extracted,$(1)) $(SIMPLIFY) $$@
endef
$(foreach p,$(PORTED),$(eval $(call PORT_RULES,$(p))))

# The OCaml that the extracted files call (runtime/port_monad.ml), and the
# empty module that some of them open (runtime/port_abbreviations.ml).
$(B)/check/port_%.cmi: runtime/port_%.ml tools/check.sh
	@mkdir -p $(B)/check
	@CMI_ROOT='$(CMI_ROOT)' OCAMLC='$(OCAMLC)' RUNTIME='$(B)/check' tools/check.sh --runtime $<

# The OCaml text that a ported file gives and Rocq copies without reading
# it (a block of OCaml, the strings of a directive of the extraction):
# each text is the lines of the compiler's file that the note before it
# names, or the setter of a record update, or the form of a type whose
# definition the file gives, or stands under a mark; a mark verbatim, type
# or update is an error if every text under it is checked so (a mark init,
# decl or unported may stay). tools/given.py says how, and what it does
# not establish. It reads decl/UPDATES.tsv and decl/DONOR-TOKENS.tsv, and
# nothing that Rocq or OCaml makes: [make given] alone does not ask Rocq
# for the dependencies of the files.
given:
	$(PYTHON) tools/given.py $(addsuffix .v,$(PORTED))

# The note of lines before each definition of a ported file, and before
# each clause [with f] of a Fixpoint: the lines
# where the compiler's file defines the thing of that name, which
# decl/DONOR-ITEMS.tsv has from the typed tree. tools/lines.py says how,
# which definitions it does not judge, and what it does not establish. It
# reads that table and decl/DONOR-TOKENS.tsv, and nothing that Rocq or
# OCaml makes: [make lines] alone does not ask Rocq for the dependencies
# of the files.
lines:
	$(PYTHON) tools/lines.py $(addsuffix .v,$(PORTED))

# The first comment of a ported file, and of the file of its abbreviations
# of modules, names the donor and the text of the donor that the file
# follows, by the name that Git gives that text. tools/follows.py compares
# both with the tree: a donor that has changed in any byte stops [make]
# until the change is carried over and the new name written. It reads
# nothing that Rocq or OCaml makes: [make follows] alone does not ask Rocq
# for the dependencies of the files.
follows:
	$(PYTHON) tools/follows.py $(addsuffix .v,$(PORTED))

# Every shell script of the folder begins with `set -eu`: the shell then
# stops it at a variable that is not set, and at a command that fails
# where the shell looks at the status of the command (not in a pipe, in a
# substitution or in a test: GUIDE.md, section 6). tools/shells.py says
# what a shell script is, and what the check does not say. It is the
# first target of [make], so a make stops there before Rocq compiles a file
# (make asks Rocq for the dependencies of the files before any target). It
# reads nothing that Rocq or OCaml makes: [make shells] alone does not ask
# Rocq for the dependencies of the files.
shells:
	$(PYTHON) tools/shells.py

# What a declared exception may carry. The real monad can raise, make a
# value of and handle an exception only if its argument has a type for
# which monad/real/Port_monad.v has an instance of the class Carried (unit,
# string): for another type Rocq refuses each use in the real build
# (monad/real/Kit_refuses.v), and a file that only declares the exception
# would pass. So each declaration of an exception in decl/ and in a ported
# file must be [Parameter E : exception T.] with T one of those types, and
# no such file may name the class (an instance made there would give the
# type a second way to be carried). tools/exceptions.py says how; it first
# tries itself on made-up texts. It reads the kit and the .v files, and
# nothing that Rocq or OCaml makes: [make exceptions] alone does not ask
# Rocq for the dependencies of the files.
exceptions:
	$(PYTHON) tools/exceptions.py --self-test
	$(PYTHON) tools/exceptions.py monad/real/Port_monad.v $(addsuffix .v,$(DECL) $(PORTED))

# A function that is given its first arguments only (pappN) runs nothing
# if its definition has more parameters. tools/lint.py checks that against
# the compiler's definitions (decl/ARITIES.tsv). For a function of a ported
# file the definition that is linked is the extracted one: this compares
# each such use with it; and each use of a function of the file itself,
# which the lint leaves to it, with the file's own extracted text; and
# each use of a function of the standard library, for which the table has
# no number, with the tree's own stdlib/. tools/papp.py says how.
papp: $(EXTRACTED)
	$(PYTHON) tools/papp.py --extracted $(addsuffix .v,$(PORTED))

# ---- the table --------------------------------------------------------

table: PROGRESS.md
PROGRESS.md: real id $(EXTRACTED) $(CHECKED) tools/progress.sh
	tools/progress.sh $(SIMPLIFY) $(B) > $@

# What each ported file carries over as text from the file that it follows:
# the leading notice and the comments (tools/comments.py).
comments:
	$(PYTHON) tools/comments.py $(SIMPLIFY)

clean:
	rm -rf $(B)
