# Libraries
REF_ROOT := ../..
INCLUDE := -I . -I $(REF_ROOT)/refiner -I ../tactic
OCAMLFLAGS := -g -root $(REF_ROOT)
OCAMLC := $(REF_ROOT)/filter/prlcomp.run
CAMLP4 := $(REF_ROOT)/filter/prlcomp.run -E -root $(REF_ROOT)

# Common files
MLZFILES :=\
	base_theory

# Library files
LMFILES :=\
	nuprl_font\
	base_dform\
	base_dtactic\
	base_theory

# Name of main libraris
MAIN = tactics

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	del -f *.p4* *.pp*

# Add dependency for parser
$(addsuffix .cmiz, $(MFILES)) $(addsuffix .cmoz, $(MFILES)): $(REF_ROOT)/filter/prlcomp.cma
$(addsuffix .p4i, $(MFILES)) $(addsuffix .p4, $(MFILES)): $(REF_ROOT)/filter/prlcomp.cma

# Real makefile
include ../../mk/config
include Makefile.dep
