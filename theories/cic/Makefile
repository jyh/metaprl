#
# Libraries
#
DIR := theories/itt
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../base $(SUPPORT_INCL)
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	cic_lambda\
	cic_ind_type

ifeq ($(TESTS_ENABLED),YES)
#	MPFILES:= $(MPFILES)\
#	itt_bugs\
#	jprover_tests\
#	itt_test\

endif

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep

