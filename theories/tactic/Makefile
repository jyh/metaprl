# Libraries
REF_ROOT := ../..
INCLUDE := -I . -I $(REF_ROOT)/refiner
OCAMLFLAGS := -g -root $(REF_ROOT)
OCAMLC := $(REF_ROOT)/filter_p4/prlcomp.run
CAMLP4 := $(REF_ROOT)/filter_p4/prlcomp.run -E

# Types files
MLZFILES :=\
	tactic_type

# Library files
LMFILES :=\
	tactic_cache\
	tactic_type\
	sequent\
	tacticals\
	var\
	options

# Name of main libraris
MAIN = tactics

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	del -f *.p4* *.pp*

# Add dependency for parser
$(addsuffix .cmiz, $(MFILES)) $(addsuffix .cmoz, $(MFILES)): $(REF_ROOT)/filter_p4/prlcomp.cma
$(addsuffix .p4i, $(MFILES)) $(addsuffix .p4, $(MFILES)): $(REF_ROOT)/filter_p4/prlcomp.cma

# Real makefile
include ../../mk/config
include Makefile.dep
