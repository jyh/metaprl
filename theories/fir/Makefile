#
# Libraries
#
DIR := theories/fir
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../tactic -I ../base -I ../ocaml
OCAMLDEPFLAGS := -prl

# Library files
MPFILES := \
   mfir_auto \
   mfir_bool \
   mfir_int \
   mfir_list \
   mfir_int_set \
   mfir_ty \
   mfir_exp \
   mfir_util \
   mfir_termOp_base \
   mfir_termOp \
   mfir_sequent \
   mfir_tr_base \
   mfir_tr_types \
   mfir_tr_atom \
   mfir_tr_store \
   mfir_tr_exp \
   mfir_theory \
   mfir_test

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

# Clean out generated files.
clean::
	$(RM) mfir_theory.ml mfir_theory.mli
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
