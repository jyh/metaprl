#
# Libraries
#
ROOT := ../..
INCLUDE := -I . -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Common files
MLZFILES :=\
	itt_theory

# Library files
NLFILES :=\
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
	itt_soft\
	itt_logic\
	itt_ext_equal\
	itt_int\
	itt_isect\
	itt_prec\
	itt_srec\
	itt_quotient\
	itt_list\
	itt_theory\
	itt_redrules

# Name of main libraris
MAIN = itt

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	del -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
