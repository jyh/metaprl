#
# Libraries
#
DIR := theories/fol
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../itt -I ../boot -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	sil_state\
	sil_programs\
	sil_sos\
	sil_itt_state\
	sil_itt_sos\
	sil_state_types\
	sil_types\
	sil_itt_state_types

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
