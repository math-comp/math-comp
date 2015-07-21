H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

ifeq "$(shell $(COQBIN)/coqtop -v | head -1 | grep trunk | wc -l | sed 's/ *//g')" "1"
V=trunk
else
V=$(shell $(COQBIN)/coqtop -v | head -1 | \
  sed 's/.*version \([0-9]\.[0-9]\)[^ ]* .*/v\1/')
endif

ifeq "$V" "v8.4"
COQDEP=../etc/utils/ssrcoqdep
else
COQDEP=$(COQBIN)/coqdep
endif

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

.DEFAULT_GOAL := all

%:
	$(H)[ -e Makefile.coq ] || $(call coqmakefile)
	# Override COQDEP to find only the "right" copy .ml files
	$(H)MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq $* \
		COQDEP='$(COQDEP) -exclude-dir plugin -c'

define coqmakefile
	(echo "Generating Makefile.coq for Coq $(V) with COQBIN=$(COQBIN)";\
	ln -sf ssreflect/plugin/$(V)/ssreflect.mllib .;\
	ln -sf ssreflect/plugin/$(V)/ssrmatching.mli .;\
	ln -sf ssreflect/plugin/$(V)/ssrmatching.ml4 .;\
	ln -sf ssreflect/plugin/$(V)/ssreflect.ml4 .;\
	$(COQBIN)/coq_makefile -f Make -o Makefile.coq)
endef

clean:
	$(H)MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq clean
	$(H)rm -f Makefile.coq
