ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif


ifeq "$(shell $(COQBIN)/coqtop -v | head -1 | grep trunk | wc -l)" "1"
V=trunk
else
V=$(shell $(COQBIN)/coqtop -v | head -1 | \
  sed 's/.*version \([0-9]\.[0-9]\)[^ ]* .*/v\1/')
endif

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

%:
	@[ -e Makefile.coq ] || $(call coqmakefile)
	@[ Make -ot Makefile.coq ] || $(call coqmakefile)
	@MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq $*

define coqmakefile
	(echo "Generating Makefile.coq for Coq $(V) with COQBIN=$(COQBIN)";\
	cp Make Make.coq;\
	echo -I plugin/$(V)/src >> Make.coq;\
	echo plugin/$(V)/src/ssreflect.mllib >> Make.coq;\
	echo plugin/$(V)/src/ssrmatching.mli >> Make.coq;\
	echo plugin/$(V)/src/ssrmatching.ml4 >> Make.coq;\
	echo plugin/$(V)/src/ssreflect.ml4 >> Make.coq;\
	$(COQBIN)/coq_makefile -f Make.coq -o Makefile.coq)
endef


