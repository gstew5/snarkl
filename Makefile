toplevel:
	cabal sandbox init; \
	cabal install

snarky:
	cd cppsrc; \
	make

test: toplevel snarky
	cabal test

bench: toplevel
	cabal bench
