#
# Don't need any libraries.
#
DIR := theories/pcaml_sos
ROOT := ../..
INCLUDE := -I .

# Common files
MLZFILES :=\
	ocaml\
	ocaml_df\
	ocaml_theory

# Library files
MPFILES :=\
	ocaml\
	ocaml_base_df\
	ocaml_expr_df\
	ocaml_patt_df\
	ocaml_type_df\
	ocaml_mt_df\
	ocaml_me_df\
	ocaml_sig_df\
	ocaml_str_df\
	ocaml_df\
	ocaml_logic\
	ocaml_base_sos\
	ocaml_expr_sos\
	ocaml_patt_sos\
	ocaml_type_sos\
	ocaml_mt_sos\
	ocaml_me_sos\
	ocaml_sig_sos\
	ocaml_str_sos\
	ocaml_theory

# Name of main libraris
MAIN = ocaml

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
