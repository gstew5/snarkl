GHC=ghc

GHC_OPTIONS=-Werror -Wall \
  -fno-warn-missing-signatures \
  -fno-warn-unused-do-bind \
  -O2

GHC_PROF_OPTIONS=-prof -fprof-auto

all:
	$(GHC) $(GHC_OPTIONS) Main.hs

prof:
	$(GHC) $(GHC_OPTIONS) $(GHC_PROF_OPTIONS) Main.hs

clean:
	rm *.o *.hi *~ main.exe
