#
# No special includes
#
DIR := theories/tactic
ROOT := ../..
INCLUDE := -I . -I $(ROOT)/lib -I $(CAMLP4LIB)
OCAMLDEPFLAGS := -prl_init

# Library files
MLZFILES :=\
	thread_refiner_sig

NLFILES :=\
	thread_refiner_sig\
	thread_refiner_null\
	thread_refiner_tree\
	remote_refiner\
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
