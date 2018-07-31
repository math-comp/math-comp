# -*- Makefile -*-

# setting variables
COQPROJECT?=Make
BEFOREMAKEFILES+=Makefile.coqdep
OTHERCLEAN+=Makefile.coqdep
COQMAKEOPTIONS=--no-print-directory

# Main Makefile
include ../Makefile.common

# --------------------------------------------------------------------
# this sets variable V (coq version) and MLLIBEXTRA
# assuming SSR is set to the directory which contains the ssreflect package
SSR=.
include Makefile.detect-coq-version
COQMAKEFILEOPTIONS=$(MLLIBEXTRA)

Makefile.coqdep:
	echo "COQDEP=$(COQDEP) -exclude-dir ssreflect/plugin -c" > Makefile.coqdep
