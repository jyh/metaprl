#
# Base theories.
#
DIR := theories/base
ROOT := ../..
INCLUDE := -I . -I ../tactic -I ../ocaml -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Common files
MLZFILES :=\
	base_theory

# Library files
MPFILES :=\
	typeinf\
	nuprl_font\
	base_dform\
	summary\
	base_auto_tactic\
	base_dtactic\
	base_cache\
	base_rewrite\
	base_theory

# Name of main libraris
MAIN = base

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
