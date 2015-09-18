toplevel:
	cabal sandbox init; \
	cabal install

snarky: 
	cd cppsrc; \
	make

test: toplevel snarky
	cabal test

bench: toplevel snarky
	cabal bench 2> /dev/null

clean:
	cd cppsrc; \
	make clean; \
	cd ..; \
	cabal clean

clean-all: clean
	rm -rf depsrc; \
	rm -rf depinst; \
	cabal sandbox delete

.PHONY: toplevel snarky test bench clean clean-all
