#
# No special includes
#
ROOT := ../..
INCLUDE :=
OCAMLDEPFLAGS := -prl

# Types files
MLZFILES :=\
	tactic_type

# Library files
NLFILES :=\
	tactic_cache\
	tactic_type\
	sequent\
	tacticals\
	var\
	options

# Name of main libraries
MAIN = tactics

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
