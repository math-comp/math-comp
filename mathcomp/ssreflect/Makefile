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

OLD_MAKEFLAGS:=$(MAKEFLAGS)
MAKEFLAGS+=-B

.DEFAULT_GOAL := all

%:
	$(H)[ -e Makefile.coq ] || $(call coqmakefile)
	# Override COQDEP to find only the "right" copy .ml files
	$(H)MAKEFLAGS=$(OLD_MAKEFLAGS) $(MAKE) --no-print-directory \
		-f Makefile.coq $* \
		COQDEP='$(COQBIN)/coqdep -exclude-dir plugin -c'

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
