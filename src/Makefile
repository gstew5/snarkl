GHC=ghc

GHC_OPTIONS=-Werror -Wall \
  -fno-warn-missing-signatures \
  -fno-warn-unused-do-bind \
  -funbox-strict-fields \
  -rtsopts \
  -threaded \
  -O \
  -optc-O3

GHC_PROF_OPTIONS=-prof -fprof-auto

HADDOCK=haddock

HADDOCK_OPTS=-o doc --html

all:
	$(GHC) $(GHC_OPTIONS) Main.hs

test:   all keccak
	./Main && time app/keccak/Main

keccak:
	$(GHC) $(GHC_OPTIONS) app/keccak/Main.hs
doc:
	$(HADDOCK) $(HADDOCK_OPTS) *.hs

debug:
	$(GHC) Main.hs

keccak-debug:
	$(GHC) app/keccak/Main.hs

prof:
	$(GHC) $(GHC_OPTIONS) $(GHC_PROF_OPTIONS) Main.hs

keccak-prof:
	$(GHC) $(GHC_OPTIONS) $(GHC_PROF_OPTIONS) app/keccak/Main.hs

clean:
	rm *.o *.hi *~ main.exe doc/* app/*/*.o app/*/*.hi app/*/main.exe
