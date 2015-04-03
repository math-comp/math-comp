
.PHONY: ssreflect algebra fingroup all odd_order solvable field character discrete real_closed ssrtest

export COQPATH=$(PWD)/..

all: ssreflect algebra fingroup odd_order solvable field character discrete real_closed ssrtest
	$(MAKE) -C $@

ssreflect:
	$(MAKE) -C $@

algebra: fingroup
	$(MAKE) -C $@

fingroup: discrete
	$(MAKE) -C $@

odd_order: field
	$(MAKE) -C $@

solvable: algebra
	$(MAKE) -C $@

field: solvable
	$(MAKE) -C $@

character: field
	$(MAKE) -C $@

discrete: ssreflect
	$(MAKE) -C $@

real_closed: algebra
	$(MAKE) -C $@

ssrtest: algebra
	$(MAKE) -C $@
