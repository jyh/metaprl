#
# Libraries
#
DIR := theories/reflect_itt
ROOT := ../..
INCLUDE := -I . -I ../itt -I ../boot -I ../tactic -I ../ocaml -I ../base
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
include $(ROOT)/mk/rules
include Makefile.dep
