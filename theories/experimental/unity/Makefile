#
# Base theories.
#
DIR := theories/experimental/unity
ROOT := ../../..

include $(ROOT)/mk/preface

INCLUDE := -I . $(SUPPORT_INCL) -I $(ROOT)/lib -I ../../base -I ../compile
OCAMLDEPFLAGS := -prl

include Files

# Common files
MLZFILES :=\

# Library files
MPFILES := $(CORE_FILES)

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
