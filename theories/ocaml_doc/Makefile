#
# Don't need any libraries.
#
DIR := theories/ocaml_doc
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../ocaml -I ../tactic -I ../base
OCAMLDEPFLAGS := -prl
PRLCFLAGS := -v

# Common files
MLZFILES :=

# Library files
MPFILES :=\
	ocaml_doc_intro\
	ocaml_doc_expr1\
	ocaml_doc_var1\
	ocaml_doc_patt1\
	ocaml_doc_expr2\
	ocaml_doc_expr3\
	ocaml_doc_exn1\
	ocaml_doc_expr4\
	ocaml_doc_io1\
	ocaml_doc_mod1\
	ocaml_doc_mod2\
	ocaml_doc_class1

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
