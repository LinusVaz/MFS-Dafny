DAFNY ?= $(HOME)/.vscode/extensions/dafny-lang.ide-vscode-3.5.4/out/resources/4.11.0/github/dafny/Dafny
OPTS ?=
DFY ?= $(firstword $(filter-out Io.dfy,$(wildcard *.dfy)))
STEM := $(basename $(notdir $(DFY)))
NATIVE_CS ?= $(wildcard *Native.cs)
OUTPUT_SUFFIXES := .exe .mdb -cs.dtr .cs .dll .deps.json .runtimeconfig.json .pdb .csproj
GENERATED = $(STEM) $(foreach suffix,$(OUTPUT_SUFFIXES),$(STEM)$(suffix))
ALL_STEMS := $(basename $(filter-out Io.dfy,$(wildcard *.dfy)))
ALL_GENERATED = $(foreach stem,$(ALL_STEMS),$(stem) $(foreach suffix,$(OUTPUT_SUFFIXES),$(stem)$(suffix)))

.PHONY: compile clean clean-all

compile:
	$(DAFNY) $(OPTS) $(DFY) $(NATIVE_CS)

%: %.dfy
	$(MAKE) compile DFY=$<

clean:
	rm -rf obj $(GENERATED)

clean-all:
	rm -rf obj $(ALL_GENERATED)
