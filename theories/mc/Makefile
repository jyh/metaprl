#
# Libraries
#
DIR := theories/mc
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../itt -I ../tactic -I ../base -I ../ocaml
OCAMLDEPFLAGS := -prl

# Library files
MPFILES := \
   mc_term_op \
   mc_set \
   fir_ty \
   fir_exp \
   fir_eval \
   fir_deadcode \
   fir_const_elim \
   mc_theory \
   fir_test

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
