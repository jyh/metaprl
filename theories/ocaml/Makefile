#
# Don't need any libraries.
#
DIR := theories/ocaml
ROOT := ../..
INCLUDE := -I . -I ../tactic -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl
PRLCFLAGS := -v

# Common files
MLZFILES :=\
	ocaml\
	ocaml_df

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
	ocaml_df

# Name of main libraris
MAIN = ocaml_df

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
