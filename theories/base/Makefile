#
# Base theories.
#
INCLUDE := -I . -I ../tactic -I ../ocaml -I $(NLLIB)
OCAMLDEPFLAGS := -prl

# Common files
MLZFILES :=\
	base_theory

# Library files
NLFILES :=\
	typeinf\
	nuprl_font\
	base_dform\
	summary\
	base_dtactic\
	base_theory\
	evaluator

# Name of main libraris
MAIN = base

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	del -f *.p4* *.pp*

# Real makefile
include ../../mk/config
include Makefile.dep
