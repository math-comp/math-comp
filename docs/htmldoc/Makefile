H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

SRC=$(shell cd ../mathcomp; ls */*.v | grep -v attic/)
HEAD=$(shell git symbolic-ref HEAD)
ifeq "$(HEAD)" "refs/heads/master"
LAST=$(shell git tag -l --sort=v:refname "mathcomp-*" | tail -n 1)
RELEASED=$(shell git show $(LAST):mathcomp/Make | grep 'v *$$' | cut -d / -f 2 | cut -d . -f 1)
endif

all:
	$(H) git diff-index --quiet HEAD ||\
		(echo error: uncommitted files; exit 1)
	$(H) cd ../mathcomp;\
		$(COQBIN)/coqdep -R . mathcomp $(SRC) 2>/dev/null |\
			grep -v vio: > ../htmldoc/depend
	$(H) cat depend | ./buildlibgraph cytoscape $(RELEASED) > depend.js
	$(H) . ../etc/utils/builddoc_lib.sh; \
		cd ../mathcomp; mangle_sources $(SRC)
	$(H) make -C ../mathcomp clean
	$(H) make -C ../mathcomp -j2
	$(H) cd ../mathcomp; $(COQBIN)/coqdoc -t "Mathematical Components"\
	       	-g --utf8 -R . mathcomp \
        	--parse-comments \
		--multi-index $(SRC) -d ../htmldoc/
	$(H) cp ../etc/artwork/coqdoc.css .
	$(H) cd ../mathcomp; git checkout $(SRC)
	

