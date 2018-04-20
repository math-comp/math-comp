H=@

ifeq "$(COQBIN)" ""
COQBIN=$(dir $(shell which coqtop))/
endif

SRC=$(shell grep 'v *$$' ../../mathcomp/Make)

all:
	$(H) git diff-index HEAD ||\
		(echo error: uncommitted files; exit 1)
	$(H) cd ../../mathcomp;\
		$(COQBIN)/coqdep -R . mathcomp $(SRC) 2>/dev/null |\
			grep -v vio: > ../docs/htmldoc/depend
	$(H) cat depend | ./buildlibgraph cytoscape $(SRC) > depend.js
	$(H) . ../../etc/utils/builddoc_lib.sh; \
		cd ../../mathcomp; mangle_sources $(SRC)
	$(H) make -C ../../mathcomp clean
	$(H) make -C ../../mathcomp -j2
	$(H) cd ../../mathcomp; \
		$(COQBIN)/coqdoc -t "Mathematical Components"\
	       	-g --utf8 -R . mathcomp \
        	--parse-comments \
		--multi-index $(SRC) -d ../docs/htmldoc/
	$(H) cp ../../etc/artwork/coqdoc.css .
	$(H) cd ../../mathcomp; git checkout $(SRC)
	

