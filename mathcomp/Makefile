# -*- Makefile -*-

# setting variables
COQPROJECT?=Make
COQMAKEOPTIONS=--no-print-directory

# Main Makefile
include Makefile.common

# --------------------------------------------------------------------
# this sets variables COQVERSION and MLLIBEXTRA
# assuming PLUGIN is set to the directory which contains the plugins
# and SSR is set to the directory of the ssreflect package
PLUGIN=../plugin
SSR=ssreflect
include ssreflect/Makefile.detect-coq-version
COQMAKEFILEOPTIONS=$(MLLIBEXTRA)
