#
# Libraries
#
DIR := theories/itt
ROOT := ../..
INCLUDE := -I . -I ../tactic -I ../ocaml -I ../base
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	itt_squash\
	itt_equal\
	itt_struct\
	itt_subtype\
	itt_void\
	itt_unit\
	itt_atom\
	itt_set\
	itt_union\
	itt_rfun\
	itt_dfun\
	itt_fun\
	itt_dprod\
	itt_dprod_imp\
	itt_prod\
	itt_logic\
	itt_well_founded\
	itt_decidable\
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
	itt_esquash\
	itt_list\
	itt_list2\
	itt_derive\
	itt_prop_decide\
	itt_fset\
	itt_theory\
	itt_collection\
	itt_test\
	itt_sort

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
