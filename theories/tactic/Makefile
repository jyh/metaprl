#
# No special includes
#
DIR := theories/tactic
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE = -I . -I ../boot -I $(ROOT)/lib -I $(CAMLP4LIB)
OCAMLDEPFLAGS := -prl_init

# Library files
MPFILES :=\
	tactic_cache\
	var\
	mptop\
	perv\
	top_tacticals\
	top_conversionals\
	nuprl_font

# Name of main libraries
MAIN = tactics

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
