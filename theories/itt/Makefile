#
# Libraries
#
DIR := theories/itt
ROOT := ../..
INCLUDE := -I . -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	itt_squash\
	itt_equal\
	itt_subtype\
	itt_struct\
	itt_void\
	itt_unit\
	itt_atom\
	itt_set\
	itt_rfun\
	itt_dfun\
	itt_fun\
	itt_dprod\
	itt_prod\
	itt_union\
	itt_logic\
	itt_bool\
	itt_ext_equal\
	itt_int\
	itt_int_bool\
	itt_atom_bool\
	itt_arith\
	itt_isect\
	itt_tunion\
	itt_bisect\
	itt_bunion\
	itt_w\
	itt_prec\
	itt_srec\
	itt_quotient\
	itt_list\
	itt_list2\
	itt_derive\
	itt_prop_decide\
	itt_fset\
	itt_theory\
	collection\
	itt_test

# Name of main libraris
MAIN = itt

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
