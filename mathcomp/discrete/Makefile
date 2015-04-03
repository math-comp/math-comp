H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif


VERSION_Coq = $(shell $(COQBIN)/coqtop -v | head -1 | sed 's/.*version \([0-9]\.[0-9]\)[^ ]* .*/v\1/')

ifeq "$(VERSION_Coq)" ""
$(error no version number found for coq)
endif

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

.DEFAULT_GOAL := all

%:
	sed -i -e "s/^(\*$(VERSION_Coq) *\(.*\) *\*)/\1/" *.v
	$(H)[ -e Makefile.coq ] || $(COQBIN)/coq_makefile -f Make -o Makefile.coq
	$(H)MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq $*

.PHONY: clean
clean:
	$(H)MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq clean
	$(H)rm -f Makefile.coq

