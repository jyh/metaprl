#
# Libraries
#
DIR := theories/fol
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../itt -I ../boot -I ../base $(SUPPORT_INCL) -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	fol_type\
	fol_false\
	fol_true\
	fol_implies\
	fol_and\
	fol_or\
	fol_not\
	fol_struct\
	fol_prop\
	fol_pred\
	fol_all\
	fol_exists\
	fol_theory\
	fol_itt_type\
	fol_itt_false\
	fol_itt_true\
	fol_itt_and\
	fol_itt_or\
	fol_itt_implies\
	fol_itt_prop\
	cfol_magic\
	cfol_theory\
	cfol_itt_base\
	cfol_itt_and\
	cfol_itt_all

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
