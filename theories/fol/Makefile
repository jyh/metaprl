#
# Libraries
#
DIR := theories/fol
ROOT := ../..
INCLUDE := -I . -I ../itt -I ../boot -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
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
	fol_univ\
	fol_all\
	fol_exists\
	fol_struct\
	fol_ctheory\
	fol_class\
	fol_theory

# Name of main libraris
MAIN = fol

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
