#
# Libraries
#
DIR := theories/mc
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../itt -I ../tactic -I ../base -I ../ocaml -I ../phobos
OCAMLDEPFLAGS := -prl

# Library files
MPFILES := \
   mp_mc_base \
   mp_mc_theory

#MPFILES := \
#   mp_mc_base \
#   mp_mc_fir_base \
#   mp_mc_fir_ty \
#   mp_mc_fir_exp \
#   mp_mc_fir_prog \
#   mp_mc_fir_eval \
#   mp_mc_deadcode \
#   mp_mc_const_elim \
#   mp_mc_theory

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa


# Clean out generated files, including symlinks.
clean::
	$(RM) mp_mc_theory.ml mp_mc_theory.mli *.exec
	$(MAKE) -C tests clean

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
