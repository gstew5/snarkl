#********************************************************************************
# Makefile adapted from the accountable algorithms system.
#********************************************************************************
#* @author     Joshua A. Kroll
#*             and contributors.
#*******************************************************************************/

CXXFLAGS += -O3 -Wall -Wextra -Wno-unused-parameter -Wno-comment -march=native -mtune=native -std=c++11 -DDEBUG

DEPINST=/usr

LDFLAGS += -L $(DEPINST)/lib -Wl,-rpath $(DEPINST)/lib
LDLIBS += -lgmpxx -lgmp -lsnark -lzm
CXXFLAGS += -I $(DEPINST)/include -I $(DEPINST)/include/libsnark -I src -DUSE_ASM -DCURVE_BN128 -DBN_SUPPORT_SNARK -g

SRCS= \
	snarky.cpp

EXECUTABLES= \
	snarky

OBJS=$(patsubst %.cpp,%.o,$(SRCS))

all: bindir $(EXECUTABLES)

bindir:
	mkdir -p bin

# In order to detect changes to #include dependencies. -MMD below generates a .d file for .cpp file. Include the .d file.
-include $(SRCS:.cpp=.d)

$(OBJS): %.o: %.cpp
	$(CXX) -o $@ $< -c -MMD $(CXXFLAGS)

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
	rm -rf bin

# Clean all, including locally-compiled dependencies
clean-all: clean
	rm -fr $(DEPSRC) $(DEPINST)

.PHONY: all clean clean-all
