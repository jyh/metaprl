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
	tactic_cache\
	perv\
	nuprl_font\
	base_dform\
	comment\
	summary\
	var\
	mptop\
	top_tacticals\
	top_conversionals

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
