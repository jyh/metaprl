#
# No special includes
#
ROOT := ../..
INCLUDE := -I $(ROOT)/lib -I .
OCAMLDEPFLAGS := -prl_init

# Library files
NLFILES :=\
	perv\
	tactic_cache\
	tactic_type\
	sequent\
	tacticals\
	var\
	rewrite_type\
	conversionals

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
