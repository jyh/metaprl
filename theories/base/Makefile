INCLUDE := -I . -I ../tactic

# Common files
MLZFILES :=\
	base_theory

# Library files
NLFILES :=\
	typeinf\
	nuprl_font\
	base_dform\
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
