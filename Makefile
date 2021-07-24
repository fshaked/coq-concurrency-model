COQTHEORIES  := $(shell find . -iname '*.v')
COQMODULE    := ConcModel

COQBIGML := $(OPAM_SWITCH_PREFIX)/.opam-switch/sources/coq/plugins/extraction/big.ml

all: proof main.native
.PHONY: all

opam-get-deps:
	opam pin add coq 8.10.1
	opam pin add coq-itree 3.0.0
	opam install coq-bbv coq-record-update
.PHONY: opam-get-deps

%.vo: %.v coq.mk
	$(MAKE) -f coq.mk $@

proof: coq.mk
	$(MAKE) -f coq.mk $(COQTHEORIES:.v=.vo)
.PHONY: proof

_CoqProject: $(COQTHEORIES)
	{ echo '-R src/ $(COQMODULE)'; \
	  echo '-R lib/ $(COQMODULE)'; \
	  echo '-arg -w'; \
	  echo '-arg all'; \
	  echo $(COQTHEORIES); \
	} > $@

coq.mk: _CoqProject
	coq_makefile -f $< -o $@

main.native main.byte main.d.byte: proof
	mkdir -p import_coq_ml
	cp $(COQBIGML) import_coq_ml/
	ocamlbuild -package num $@

debug-main: main.d.byte
	ocamldebug $<
.PHONY: debug-main

clean-extracted:
	rm -f extracted_ocaml/*
	ocamlbuild -clean
.PHONY: clean-extracted
clean: clean-extracted

clean:
	-$(MAKE) -f coq.mk clean
	rm -f coq.mk coq.mk.conf _CoqProject
	find . -name "*.vio" -type f -delete
	find . -name "*.v.d" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
	find . -name ".*.aux" -type f -delete
.PHONY: clean
