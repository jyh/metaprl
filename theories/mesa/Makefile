#
# Libraries
#
DIR := theories/mesa
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../itt -I ../base $(SUPPORT_INCL)
OCAMLDEPFLAGS := -prl

# Library files
include Files

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep

