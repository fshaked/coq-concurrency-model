COQTHEORIES  := $(shell find . -iname '*.v')
COQMODULE    := ConcModel

all: proof main.native
.PHONY: all

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

main.native: proof
	ocamlbuild $@

clean-extracted:
	rm -f extracted_ocaml/*
clean: clean-extracted
.PHONY: clean-extracted

clean:
	-$(MAKE) -f coq.mk clean
	rm -f coq.mk coq.mk.conf _CoqProject
	find . -name "*.vio" -type f -delete
	find . -name "*.v.d" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
	find . -name ".*.aux" -type f -delete
.PHONY: clean
