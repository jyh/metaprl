#
# Libraries
#
DIR := theories/reflect_itt
ROOT := ../..
INCLUDE := -I . -I ../itt -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Library files
NLFILES :=\
	refl_term

# Name of main libraris
MAIN = reflect_itt

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
