# Libraries
REF_ROOT := ../..
INCLUDE := -I . -I $(REF_ROOT)/mllib -I $(REF_ROOT)/refiner -I ../tactic -I ../base -I ../itt
OCAMLFLAGS := -g -root $(REF_ROOT)
OCAMLC := $(REF_ROOT)/filter/prlcomp.run
CAMLP4 := $(REF_ROOT)/filter/prlcomp.run -E -root $(REF_ROOT)

# Program files
PFILES :=\
	rw_beta

# Libraries
MLLIBS :=\
	../../mllib/util\
	../../refiner/refiner\
	../tactic/tactics\
	../base/base\
	../itt/itt

# Name of main libraris
MAIN = rw

all: $(MAIN).run
opt: $(MAIN).opt

clean::
	del -f *.p4* *.pp*

# Add dependency for parser
$(addsuffix .cmiz, $(MFILES)) $(addsuffix .cmoz, $(MFILES)): $(REF_ROOT)/filter/prlcomp.cma
$(addsuffix .p4i, $(MFILES)) $(addsuffix .p4, $(MFILES)): $(REF_ROOT)/filter/prlcomp.cma

# Real makefile
include ../../mk/config
include Makefile.dep
