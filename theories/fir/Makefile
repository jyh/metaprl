#
# Libraries
#
DIR := theories/fir
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../itt -I ../tactic -I ../base -I ../ocaml
OCAMLDEPFLAGS := -prl

# Library files
MPFILES := \
   mfir_comment \
   mfir_basic \
   mfir_ty \
   mfir_exp \
   mfir_termOp_base \
   mfir_termOp \
   mfir_theory

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
