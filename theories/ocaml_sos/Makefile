#
# Don't need any libraries.
#
DIR := theories/ocaml_sos
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../tactic -I ../ocaml -I ../base

# Common files
MLZFILES :=

# Library files
MPFILES :=\
	ocaml_base_sos

X :=\
	ocaml_expr_sos\
	ocaml_patt_sos\
	ocaml_type_sos\
	ocaml_mt_sos\
	ocaml_me_sos\
	ocaml_sig_sos\
	ocaml_str_sos\
	ocaml_theory

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
