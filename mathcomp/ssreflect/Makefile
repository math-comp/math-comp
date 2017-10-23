H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

# this sets variable V
include Makefile.detect-coq-version
# this defined coqmakefile
include Makefile.coq-makefile

COQDEP=$(COQBIN)coqdep

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

.DEFAULT_GOAL := all

%:
	$(H)[ -e Makefile.coq ] || $(call coqmakefile,.)
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq $* \
		COQDEP='$(COQDEP) -exclude-dir plugin -c'

clean:
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq clean
	$(H)rm -f Makefile.coq
