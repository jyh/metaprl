#
# Libraries
#
DIR := theories/tptp
ROOT := ../..
INCLUDE := -I . -I ../itt -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Library files
LMFILES :=\
	tptp_type\
	tptp_parse\
	tptp_lex

MPFILES :=\
	tptp\
	tptp_load\
	tptp_cache\
	tptp_prove

# Name of main libraris
MAIN = tptp

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp* tptp_lex.ml

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
