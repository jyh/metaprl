#
# Libraries
#
DIR := theories/czf
ROOT := ../..
INCLUDE := -I . -I ../itt -I ../boot -I ../tactic -I ../ocaml -I ../base
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	czf_itt_set\
	czf_itt_eq\
	czf_itt_member\
	czf_itt_sep\
	czf_itt_union\
	czf_itt_true\
	czf_itt_false\
	czf_itt_or\
	czf_itt_and\
	czf_itt_implies\
	czf_itt_all\
	czf_itt_exists\
	czf_itt_set_ind\
	czf_itt_dall\
	czf_itt_dexists\
	czf_itt_sall\
	czf_itt_sexists\
	czf_itt_rel\
	czf_itt_axioms

# Name of main libraris
MAIN = czf

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
