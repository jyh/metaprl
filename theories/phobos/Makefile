#
# Libraries
#
DIR := theories/phobos
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../base -I ../itt $(SUPPORT_INCL)
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	phobos_base\
	phobos_theory

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep

