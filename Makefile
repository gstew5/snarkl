toplevel:
	cabal sandbox init; \
	cabal install

snarky:
	cd cppsrc; \
	make

test: snarky toplevel
	cabal test

bench: toplevel
	cabal bench

clean:
	cd cppsrc; \
	make clean; \
	cd ..; \
	cabal clean

clean-all: clean
	rm -rf depsrc; \
	rm -rf depinst; \
	cabal sandbox delete
