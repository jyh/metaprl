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
   mp_mc_fir_base \
   mp_mc_fir_ty \
   mp_mc_fir_exp \
   mp_mc_fir_prog \
   mp_mc_fir_eval \
   mp_mc_fir_phobos_exp \
   mp_mc_fir_phobos \
   mp_mc_deadcode \
   mp_mc_const_elim \
   mp_mc_theory

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa


# Clean out generated files, including symlinks.
clean::
	$(RM) *.cm* *.o *.p4* *.pp* *.exec
	$(MAKE) -C tests clean

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
