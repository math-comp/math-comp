H=@

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

.DEFAULT_GOAL := all

%:
	$(H)[ -e Makefile.coq ] || $(call coqmakefile)
# Override COQLIBS to find the "right" copy .ml files, otherwise
# coq_makefile uses only the -R in COQLIBS and ignores the -I in
# OCAMLLIBS to look for .ml files in order to generate .d files
# via coqdep
	$(H)MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq $* \
		COQLIBS='-I . -R . mathcomp.ssreflect'

define coqmakefile
	(echo "Generating Makefile.coq for Coq $(V) with COQBIN=$(COQBIN)";\
	ln -sf plugin/$(V)/ssreflect.mllib .;\
	ln -sf plugin/$(V)/ssrmatching.mli .;\
	ln -sf plugin/$(V)/ssrmatching.ml4 .;\
	ln -sf plugin/$(V)/ssreflect.ml4 .;\
	$(COQBIN)/coq_makefile -f Make -o Makefile.coq)
endef

clean:
	$(H)MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq clean
	$(H)rm -f Makefile.coq
