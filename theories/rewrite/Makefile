# Libraries
ROOT := ../..
INCLUDE := -I . -I $(ROOT)/mllib -I $(ROOT)/refiner -I $(ROOT)/library -I ../tactic -I ../base -I ../itt
OCAMLFLAGS := -g -root $(ROOT)
OCAMLC := $(ROOT)/filter/prlcomp.run
CAMLP4 := $(ROOT)/filter/prlcomp.run -E -root $(ROOT)

# Program files
PFILES :=\
	rw_beta

# Libraries
MLLIBS :=\
	$(ROOT)/mllib/util\
	$(ROOT)/refiner/refiner\
	$(ROOT)/library/library\
	../tactic/tactics\
	../base/base\
	../itt/itt

CMALIBS :=\
	unix.cma

CCLIBS :=\
	-cclib -lunix

# Name of main libraris
MAIN = rw

all: $(MAIN).run
opt: $(MAIN).opt
install:: all

clean::
	$(RM) *.p4* *.pp*

# Add dependency for parser
$(addsuffix .cmiz, $(MFILES)) $(addsuffix .cmoz, $(MFILES)): $(ROOT)/filter/prlcomp.cma
$(addsuffix .p4i, $(MFILES)) $(addsuffix .p4, $(MFILES)): $(ROOT)/filter/prlcomp.cma

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
