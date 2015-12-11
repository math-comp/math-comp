# this

R=1.6

import-doc:
	git subtree add -P htmldoc release/$(R)
	T=`git subtree split -P htmldoc release/$(R)`;\
	git subtree merge -P htmldoc --squash $$T \
		-m 'importing htmldoc from $(R)'
