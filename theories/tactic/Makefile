#
# No special includes
#
DIR := theories/tactic
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE = -I . -I $(ROOT)/lib -I $(CAMLP4LIB)
OCAMLDEPFLAGS := -prl_init

# Library files
MPFILES :=\
	perv\
	tactic_cache\
	tactic_type\
	sequent\
	var\
	rewrite_type\
	mptop\
	tacticals\
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
