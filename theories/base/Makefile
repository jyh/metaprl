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
NLFILES :=\
	typeinf\
	nuprl_font\
	base_dform\
	summary\
	base_auto_tactic\
	base_dtactic\
	base_cache\
	base_rewrite\
	base_theory\
	evaluator

# Name of main libraris
MAIN = base

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	del -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
