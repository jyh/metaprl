#
# Libraries
#
DIR := theories/kat
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../base $(SUPPORT_INCL) -I ../itt $(SUPPORT_INCL)
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	support_algebra \
	base_select \
	kat_terms \
	kat_axioms \

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep

