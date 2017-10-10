H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

# this sets variable V
include Makefile.detect-coq-version
# this defined coqmakefile
include Makefile.coq-makefile

ifeq "$V" "v8.4"
COQDEP=../../etc/utils/ssrcoqdep
else
COQDEP=$(COQBIN)coqdep
endif

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

.DEFAULT_GOAL := all

%:
	$(H)[ -e Makefile.coq ] || $(call coqmakefile,.)
	# Override COQDEP to find only the "right" copy .ml files
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq $* \
		COQDEP='$(COQDEP) -exclude-dir plugin -c'

clean:
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq clean
	$(H)rm -f Makefile.coq
