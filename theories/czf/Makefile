#
# Libraries
#
DIR := theories/czf
ROOT := ../..
INCLUDE := -I . -I ../itt -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Common files
MLZFILES :=\
	czf_theory

# Library files
NLFILES :=\
	czf_itt_set\
	czf_itt_eq\
	czf_itt_member\
	czf_itt_sep\
	czf_itt_true\
	czf_itt_false\
	czf_itt_or\
	czf_itt_and\
	czf_itt_implies\
	czf_itt_all

# Name of main libraris
MAIN = czf

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	del -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
