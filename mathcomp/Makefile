# -*- Makefile -*-

# setting variables
COQPROJECT?=Make
COQMAKEOPTIONS=--no-print-directory

# Main Makefile
include Makefile.common

# --------------------------------------------------------------------
# this sets variable V (coq version) and MLLIBEXTRA
# assuming SSR is set to the directory which contains the ssreflect package
SSR=ssreflect
include ssreflect/Makefile.detect-coq-version
COQMAKEFILEOPTIONS=$(MLLIBEXTRA)
