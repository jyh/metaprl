#
# Libraries
#
DIR := theories/experimental/compile
ROOT := ../../..

include $(ROOT)/mk/preface

INCLUDE := -I . -I ../../tactic -I ../../ocaml -I ../../base
OCAMLDEPFLAGS := -prl

# Library files
MLZFILES :=\
	m_theory

MPFILES :=\
	m_ir\
	m_cps\
	m_closure\
	m_theory\
	m_test

# Name of main libraris
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp* *.cph *.output

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
