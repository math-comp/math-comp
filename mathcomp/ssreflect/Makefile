# -*- Makefile -*-

# setting variables
COQPROJECT?=Make
COQMAKEOPTIONS=--no-print-directory

# Main Makefile
include ../Makefile.common

# --------------------------------------------------------------------
# this sets variables COQVERSION and MLLIBEXTRA
# assuming PLUGIN is set to the directory which contains the plugins
PLUGIN=../../plugin/
SSR=.
include Makefile.detect-coq-version
COQMAKEFILEOPTIONS=$(MLLIBEXTRA)
