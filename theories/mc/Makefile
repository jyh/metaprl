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
   mp_mc_term_op \
   mp_mc_set \
   fir_ty \
   fir_exp \
   fir_eval \
   fir_deadcode \
   fir_const_elim \
   mp_mc_theory \
   fir_test

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.cm* *.o *.p4* *.pp* *.exec
	$(MAKE) -C tests clean

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
