#
# No special includes
#
ROOT := ../..
INCLUDE := -I $(ROOT)/lib -I .
OCAMLDEPFLAGS := -prl_init

# Library files
NLFILES :=\
	tactic_cache\
	tactic_type\
	sequent\
	tacticals\
	rewrite_type\
	conversionals\
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
