H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

BRANCH_coq = $(shell $(COQBIN)/coqtop -v | head -1 | sed 's/.*version \([0-9]\.[0-9]\)[^ ]* .*/v\1/')

HASH_coq = $(shell echo Quit. | $(COQBIN)/coqtop 2>&1 | head -1 | sed 's/^.*(\([a-f0-9]*\)).*/\1/' )

HASH_coq_v85beta1 = eaa3d0b15adf4eb11ffb00ab087746a5b15c4d5d


ifeq "$(HASH_coq)" "$(HASH_coq_v85beta1)"
V=v8.5beta1
else
V=$(BRANCH_coq)
endif

ifeq "$V" "v8.4"
COQDEP=../../etc/utils/ssrcoqdep
else
COQDEP=$(COQBIN)/coqdep
endif

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

.DEFAULT_GOAL := all

%:
	$(H)[ -e Makefile.coq ] || $(COQBIN)/coq_makefile -f Make -o Makefile.coq
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq $* \
		COQDEP='$(COQDEP) -c'

.PHONY: clean
clean:
	$(H)MAKEFLAGS="$(OLD_MAKEFLAGS)" $(MAKE) --no-print-directory \
		-f Makefile.coq clean
	$(H)rm -f Makefile.coq

