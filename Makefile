COQTHEORIES  := $(shell find . -iname '*.v')

all: proof

%.vo: %.v coq.mk
	$(MAKE) -f coq.mk $@

proof: coq.mk
	$(MAKE) -f coq.mk $(COQTHEORIES:.v=.vo)

_CoqProject: $(COQTHEORIES)
	{ echo '-R src/ ConcModel'; \
	  echo '-arg -w'; \
	  echo '-arg all'; \
	  echo $(COQTHEORIES); \
	} > $@

coq.mk: _CoqProject
	coq_makefile -f $< -o $@

clean:
	-$(MAKE) -f coq.mk clean
	rm -f coq.mk coq.mk.conf _CoqProject
	find . -name "*.vio" -type f -delete
	find . -name "*.v.d" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.glob" -type f -delete
