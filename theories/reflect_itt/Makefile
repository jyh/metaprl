#
# Libraries
#
DIR := theories/reflect_itt
ROOT := ../..
INCLUDE := -I . -I ../itt -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Library files
MPFILES :=\
	refl_var\
	refl_raw_term\
	refl_term\
	refl_var_set\
	refl_free_vars

# Name of main libraris
MAIN = reflect_itt

all: $(MAIN).cma
opt: $(MAIN).cmxa

clean::
	$(RM) *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
