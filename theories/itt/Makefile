#
# Libraries
#
DIR := theories/itt
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../tactic -I ../ocaml -I ../base
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	itt_comment\
	itt_equal\
	itt_struct\
	itt_squash\
	itt_squiggle\
	itt_subtype\
	itt_void\
	itt_unit\
	itt_atom\
	itt_set\
	itt_union\
	itt_rfun\
	itt_dfun\
	itt_eta\
	itt_fun\
	itt_dprod\
	itt_prod\
	itt_esquash\
	itt_logic\
	itt_well_founded\
	itt_decidable\
	itt_bool\
	itt_ext_equal\
	itt_pointwise\
	itt_struct2\
	itt_struct3\
	itt_int_base\
	itt_int_ext\
	itt_int_arith\
	itt_atom_bool\
	itt_nat\
	itt_isect\
	itt_tsquash\
	itt_disect\
	itt_tunion\
	itt_bisect\
	itt_bunion\
	itt_inv_typing\
	itt_w\
	itt_prec\
	itt_srec\
	itt_quotient\
	itt_list\
	itt_list2\
	itt_derive\
	itt_prop_decide\
	itt_fset\
	itt_pointwise2\
	itt_theory\
	itt_collection\
	ctt_markov\
	itt_record_label0\
	itt_record_label\
	itt_record0\
	itt_record\
	itt_record_exm\
	itt_sort

ifeq ($(TESTS),YES)
	MPFILES:= $(MPFILES)\
	itt_bugs\
	jprover_tests\
	itt_test\

endif

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep

