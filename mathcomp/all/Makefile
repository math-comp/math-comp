# -*- Makefile -*-

COQPROJECT="Make"

# --------------------------------------------------------------------
include Makefile.common

# --------------------------------------------------------------------
COQMAKEOPTIONS=--no-print-directory

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
.PHONY: count

COQFILES := $(shell grep '.v$$' Make)

count:
	@coqwc $(COQFILES) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'

