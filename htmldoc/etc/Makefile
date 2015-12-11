VERSION=$(shell git symbolic-ref --short HEAD | cut -d / -f 2)

dist:
	cd ..; git archive --format tar --prefix mathcomp-$(VERSION)/\
	       -o mathcomp-$(VERSION).tar HEAD
	cd ..; gzip -f -9 mathcomp-$(VERSION).tar
