#
# Libraries
#
ROOT := ../..
INCLUDE := -I . -I ../tactic -I ../ocaml -I ../base -I $(ROOT)/lib
OCAMLDEPFLAGS := -prl

# Common files
MLZFILES :=\
	itt_theory

# Library files
NLFILES :=\
	itt_squash\
	itt_equal\
	itt_subtype\
	itt_struct\
	itt_void\
	itt_unit\
	itt_atom\
	itt_set\
	itt_rfun\
	itt_dfun\
	itt_fun\
	itt_dprod\
	itt_prod\
	itt_union\
	itt_soft\
	itt_logic\
	itt_bool\
	itt_ext_equal\
	itt_int\
	itt_int_bool\
	itt_arith\
	itt_isect\
	itt_prec\
	itt_srec\
	itt_quotient\
	itt_list\
	itt_theory\
	itt_redrules\
	itt_test

PFILES := test

CMXDEPS =\
	$(CAMLLIB)/unix.cmxa\
        $(CAMLLIB)/nums.cmxa\
	$(ROOT)/lib/clib.cmxa\
	$(ROOT)/lib/util.cmxa\
	$(ROOT)/lib/refiner.cmxa\
	$(ROOT)/lib/library.cmxa\
	$(ROOT)/theories/tactic/tactics.cmxa\
	$(ROOT)/theories/ocaml/ocaml_df.cmxa\
	$(ROOT)/theories/base/base.cmxa\
	nl.cmxa

CMXLIBS =\
	$(CMXDEPS)

CMADEPS =\
	$(CAMLLIB)/unix.cma\
        $(CAMLLIB)/nums.cma\
	$(ROOT)/lib/clib.cma\
	$(ROOT)/lib/util.cma\
	$(ROOT)/lib/refiner.cma\
	$(ROOT)/lib/library.cma\
	$(ROOT)/theories/tactic/tactics.cma\
	$(ROOT)/theories/ocaml/ocaml_df.cma\
	$(ROOT)/theories/base/base.cma\
	$(MAIN).cma

CMALIBS =\
	$(CMADEPS)

CMOBJS =\
	$(CMALIBS)\
	test.cmo

CMXOBJS =\
	$(CMXLIBS)\
	test.cmx

CCLIBS =\
	-cclib -lunix\
        -cclib -lnums\
	-cclib $(ROOT)/lib/clib.a

TEST = test

# Name of main libraris
MAIN = itt

all: $(MAIN).cma
opt: $(MAIN).cmxa

$(TEST).run: $(CMOBJS)
	rm -f $@
	$(OCAMLC) -o $@ -custom -linkall $(CMOBJS) $(CCLIBS)

$(TEST).opt: $(CMXOBJS)
	rm -f $@
	$(OCAMLOPT) -ccopt -p -o $@ -custom -linkall $(CMXOBJS) $(CCLIBS)

clean::
	del -f *.p4* *.pp*

# Real makefile
include $(ROOT)/mk/config
include Makefile.dep
