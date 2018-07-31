# -*- Makefile -*-

COQPROJECT="Make"

# --------------------------------------------------------------------
# this sets variable V
include ssreflect/Makefile.detect-coq-version
# this defines prepare_coqmakefile
include ssreflect/Makefile.coq-makefile
include Makefile.common

# --------------------------------------------------------------------
COQMAKEOPTIONS=--no-print-directory \
	COQDEP='$(COQDEP) -exclude-dir ssreflect/plugin -c'
COQMAKEFILEOPTIONS=$(MLLIB) $(EXTRA)

# --------------------------------------------------------------------
.PHONY: pre_makefile
BEFOREMAKEFILE=pre_makefile

pre_makefile:
	$(call prepare_coqmakefile,ssreflect)

