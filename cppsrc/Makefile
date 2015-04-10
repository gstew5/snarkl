#********************************************************************************
# Makefile for the accountable algorithms system.
#********************************************************************************
#* @author     Joshua A. Kroll
#*             and contributors (see AUTHORS).
#*******************************************************************************/

CXXFLAGS += -O3 -Wall -Wextra -Wno-unused-parameter -Wno-comment -march=native -mtune=native -std=c++11 -DDEBUG

DEPINST=~

LDFLAGS += -L $(DEPINST)/lib -Wl,-rpath $(DEPINST)/lib
LDLIBS += -lgmpxx -lgmp -lsnark -lzm
CXXFLAGS += -I $(DEPINST)/include -I $(DEPINST)/include/libsnark -I src -DUSE_ASM -DCURVE_BN128 -DBN_SUPPORT_SNARK -g

# ifneq ($(NO_GTEST),1)
# 	GTESTDIR=/usr/src/gtest
# # Recompile GTest, if we can (e.g., Ubuntu). Otherwise use precompiled one (e.g., Fedora).
# # See https://code.google.com/p/googletest/wiki/FAQ#Why_is_it_not_recommended_to_install_a_pre-compiled_copy_of_Goog .
# 	COMPILE_GTEST:=$(shell test -d $(GTESTDIR) && echo 1)   # Found GTest sourcecode?
# 	LDLIBS += -lgtest -lpthread
# endif

SRCS= \
	prover_function.cpp \
	accountable_gadgets.cpp \
	util.cpp

EXECUTABLES= \
	snarky \
#	generator \
	prover \
	verifier \
	basic_test \
    simplest_test \
	printer_integration_test

# ifneq ($(NO_GTEST),1)
# 	EXECUTABLES += \
# # Test executables go here.
# endif


OBJS=$(patsubst %.cpp,%.o,$(SRCS))

ifeq ($(strip $(COMPILE_GTEST)),1)
all: libgtest.a $(EXECUTABLES) doc
else
all: $(EXECUTABLES) doc
endif

default: $(EXECUTABLES)

doc: $(DOCS)

# In order to detect changes to #include dependencies. -MMD below generates a .d file for .cpp file. Include the .d file.
-include $(SRCS:.cpp=.d)

$(OBJS): %.o: %.cpp
	$(CXX) -o $@ $< -c -MMD $(CXXFLAGS)

# libgtest.a: $(GTESTDIR)/src/gtest-all.cc
# 	$(CXX) -I $(GTESTDIR) -c -isystem $(GTESTDIR)/include $< $(CXXFLAGS) -o $(DEPINST)/lib/gtest-all.o
# 	$(AR) -rv $(DEPINST)/lib/libgtest.a $(DEPINST)/lib/gtest-all.o


$(EXECUTABLES): %: %.o $(OBJS)
	$(CXX) -o bin/$@ $^ $(CXXFLAGS) $(LDFLAGS) $(LDLIBS)

# Clean generated files, except locally-compiled dependencies
clean:
	$(RM) \
		$(OBJS) \
		$(EXECUTABLES) \
		${patsubst %,%.o,${EXECUTABLES}} \
		${patsubst %.cpp,%.d,${SRCS}} \
		${patsubst %,%.d,${EXECUTABLES}}
#	$(RM $(DEPINST)/lib/libgtest.a $(DEPINST)/lib/gtest-all.o

# Clean all, including locally-compiled dependencies
clean-all: clean
	rm -fr $(DEPSRC) $(DEPINST)

.PHONY: all clean clean-all doc doxy lib
