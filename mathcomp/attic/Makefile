H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

.DEFAULT_GOAL := all

%:
	$(H)[ -e Makefile.coq ] || $(COQBIN)/coq_makefile -f Make -o Makefile.coq
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq $*

.PHONY: clean
clean:
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq clean
	$(H)rm -f Makefile.coq

