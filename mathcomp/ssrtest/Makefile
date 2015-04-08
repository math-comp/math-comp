MAKEFLAGS := -r

.SUFFIXES:

.PHONY: clean all config tags install

COQMAKEFILE := Makefile.coq
COQMAKE := +$(MAKE) -f $(COQMAKEFILE)

VERSION_Coq = $(shell $(COQBIN)/coqtop -v | head -1 | sed 's/.*version \([0-9]\.[0-9]\)[^ ]* .*/v\1/')

ifeq "$(VERSION_Coq)" ""
$(error no version number found for coq)
endif

all: $(COQMAKEFILE)
	$(COQMAKE) all

$(COQMAKEFILE) config:
	$(COQBIN)coq_makefile -f Make  -o $(COQMAKEFILE)

clean: $(COQMAKEFILE)
	$(COQMAKE) clean
	$(RM) -rf $(COQMAKEFILE)

tags:
	$(COQBIN)coqtags `find . -name \*.v`

install:

%: Makefile.coq
	sed -i -e "s/^(\*$(VERSION_Coq) *\(.*\) *\*)/\1/" *.v
	$(COQMAKE) $@
