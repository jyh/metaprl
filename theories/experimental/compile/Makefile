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
	m_util\
	m_ir\
	m_cps\
	m_closure\
	m_prog\
	m_dead\
	m_inline\
	m_theory\
	m_test

OTHER =\
	m_ast\
	m_post_parsing\
	m_cps\
	m_closure\
	x86_asm\
	m_x86\
	m_theory\
	m_test

# Name of main libraries
MAIN = theory

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp* *.cph *.output

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
