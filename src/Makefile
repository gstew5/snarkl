GHC=ghc

GHC_OPTIONS=-Werror -Wall \
  -fno-warn-missing-signatures \
  -fno-warn-unused-do-bind

all:
	$(GHC) $(GHC_OPTIONS) main.hs

clean:
	rm *.o *.hi *~ main.exe
