#
# No special includes
#
DIR := theories/tactic
ROOT := ../..

include $(ROOT)/mk/preface

INCLUDE = -I . -I $(ROOT)/lib -I $(CAMLP4LIB)

OCAMLFLAGS = -pp "camlp4o$(EXE) q_MLast.cmo pa_extend.cmo"

# Type files
MLZFILES :=\
	tactic_boot_sig\
	io_proof_type

# Library files
LMFILES :=\
	tactic_boot_sig\
	tactic_boot\
	sequent_boot\
	tacticals_boot\
	rewrite_boot\
	conversionals_boot\
	proof_term_boot\
	proof_boot\
	exn_boot\
	tactic_type

# Name of main libraries
MAIN = boot

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/rules
include Makefile.dep
