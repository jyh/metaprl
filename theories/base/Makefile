#
# Base theories.
#
DIR := theories/base
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../tactic -I ../ocaml -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Common files
MLZFILES :=\
	base_theory

# Library files
MPFILES :=\
	typeinf\
	base_trivial\
	base_auto_tactic\
	base_dtactic\
	base_cache\
	base_meta\
	base_rewrite\
	base_theory

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
