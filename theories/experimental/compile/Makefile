#
# Libraries
#
DIR := theories/experimental/compile
ROOT := ../../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../../tactic -I ../../ocaml -I ../../base
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	m_ir

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp* *.cph *.output

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
