# Libraries
REF_ROOT := ../..
INCLUDE := -I . -I $(REF_ROOT)/refiner -I ../tactic -I ../base
OCAMLFLAGS := -g -root $(REF_ROOT)
OCAMLC := $(REF_ROOT)/filter_p4/prlcomp.run
CAMLP4 := $(REF_ROOT)/filter_p4/prlcomp.run -E -root $(REF_ROOT)

# Common files
MLZFILES :=\
	itt_theory

# Library files
LMFILES :=\
	itt_equal\
	itt_void\
	itt_atom\
	itt_set\
	itt_rfun\
	itt_dfun\
	itt_fun\
	itt_dprod\
	itt_prod\
	itt_union\
	itt_soft\
	itt_logic\
	itt_struct\
	itt_int\
	itt_isect\
	itt_subtype\
	itt_prec\
	itt_srec\
	itt_quotient\
	itt_list\
	itt_theory

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
