#
# No special includes
#
DIR := theories/tactic
ROOT := ../..
INCLUDE := -I . -I $(ROOT)/lib 
INCAMLP4 := yes
OCAMLDEPFLAGS := -prl_init

# Library files
NLFILES :=\
	perv\
	tactic_cache\
	tactic_type\
	sequent\
	var\
	rewrite_type\
	nltop\
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
