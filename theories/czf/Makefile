#
# Libraries
#
DIR := theories/czf
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../itt -I ../boot -I ../tactic -I ../ocaml -I ../base
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	czf_itt_comment\
	czf_itt_set\
	czf_itt_eq\
	czf_itt_member\
	czf_itt_sep\
	czf_itt_true\
	czf_itt_false\
	czf_itt_or\
	czf_itt_and\
	czf_itt_implies\
	czf_itt_all\
	czf_itt_exists\
	czf_itt_fol\
	czf_itt_set_ind\
	czf_itt_dall\
	czf_itt_dexists\
	czf_itt_sall\
	czf_itt_sexists\
	czf_itt_rel\
	czf_itt_subset\
	czf_itt_empty\
	czf_itt_singleton\
	czf_itt_union\
	czf_itt_isect\
	czf_itt_pair\
	czf_itt_nat\
	czf_itt_power\
	czf_itt_axioms\
	czf_itt_theory\
	czf_itt_set_bvd\
	czf_itt_inv_image\
	czf_itt_setdiff\
	czf_itt_bool\
	czf_itt_equiv\
	czf_itt_group\
	czf_itt_group_bvd\
	czf_itt_abel_group\
	czf_itt_subgroup\
	czf_itt_coset\
	czf_itt_normal_subgroup\
	czf_itt_cyclic_subgroup\
	czf_itt_cyclic_group\
	czf_itt_hom\
	czf_itt_ker\
	czf_itt_iso\
	czf_itt_kleingroup

MLZFILES :=\
	czf_itt_fol\
	czf_itt_theory

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
