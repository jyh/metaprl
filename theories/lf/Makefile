# Libraries
ROOT := ../..
INCLUDE = -I . -I ../../refiner

# Commands
CAMLC = camlc
CAMLOPT = camlopt
CAMLDEP = ../../csltocl/cldep
CAMLLEX = camllex
CAMLYACC = camlyacc
CAMLRUN = camlrun
CAMLLIBR = camllibr
CAMLCFLAGS = -g $(INCLUDE)
CAMLOPTFLAGS = $(INCLUDE)
CAMLLIBS = ../../refiner/refiner.zo

# Commands
CSLC = cslc
CSLOPT = cslopt
CSLDEP = csldep
CSLLEX = csllex
CSLYACC = cslyacc
CSLLIBR = cslc
CSLCFLAGS = $(INCLUDE)
CSLOPTFLAGS = $(INCLUDE)
CSLLIBS = ../../refiner/refiner.cma

# For processing .prl files
PRLC.RUN = ../../refiner/prlcomp.run
PRLC = camlrun $(PRLC.RUN)
PRLCFLAGS = $(INCLUDE)

# Name of the product of this Makefile
NAME = lfLibrary

# Library files
LMFILES = \
	lf_sig\
	lf_kind\
        lf_type\
	lf_dfun

# Main files
RMFILES = main

# Library file names
LMLFILES   = $(addsuffix .ml,   $(LMFILES))
LMLIFILES  = $(addsuffix .mli,  $(LMFILES))
LPRLFILES  = $(addsuffix .prl,  $(LMFILES))
LPRLIFILES = $(addsuffix .prli, $(LMFILES))
LZSIFILES  = $(addsuffix .zsi,  $(LMFILES))
LZOFILES   = $(addsuffix .zo,   $(LMFILES))
LZIFILES   = $(addsuffix .zi,   $(LMFILES))
LZXFILES   = $(addsuffix .zx,   $(LMFILES))
LCMOFILES  = $(addsuffix .cmo,  $(LMFILES))
LCMIFILES  = $(addsuffix .cmi,  $(LMFILES))
LCMXFILES  = $(addsuffix .cmx,  $(LMFILES))

# Regular file names
RMLFILES   = $(addsuffix .ml,   $(RMFILES))
RMLIFILES  = $(addsuffix .mli,  $(RMFILES))
RPRLFILES  = $(addsuffix .prl,  $(RMFILES))
RPRLIFILES = $(addsuffix .prli, $(RMFILES))
RZSIFILES  = $(addsuffix .zsi,  $(RMFILES))
RZOFILES   = $(addsuffix .zo,   $(RMFILES))
RZIFILES   = $(addsuffix .zi,   $(RMFILES))
RZXFILES   = $(addsuffix .zx,   $(RMFILES))
RCMOFILES  = $(addsuffix .cmo,  $(RMFILES))
RCMIFILES  = $(addsuffix .cmi,  $(RMFILES))
RCMXFILES  = $(addsuffix .cmx,  $(RMFILES))

# all file names
MLFILES   = $(LMLFILES)   $(RMLFILES)   $(FMLFILES)
MLIFILES  = $(LMLIFILES)  $(RMLIFILES)  $(FMLIFILES)
PRLFILES  = $(LPRLFILES)  $(RPRLFILES)  $(FPRLFILES)
PRLIFILES = $(LPRLIFILES) $(RPRLIFILES) $(FPRLIFILES)
ZSIFILES  = $(LZSIFILES)  $(RZSIFILES)  $(FZSIFILES)
ZOFILES   = $(LZOFILES)   $(RZOFILES)   $(FZOFILES)
ZIFILES   = $(LZIFILES)   $(RZIFILES)   $(FZIFILES)
ZXFILES   = $(LZXFILES)   $(RZXFILES)   $(FZXFILES)
CMOFILES  = $(LCMOFILES)  $(RCMOFILES)  $(FCMOFILES)
CMIFILES  = $(LCMIFILES)  $(RCMIFILES)  $(FCMIFILES)
CMXFILES  = $(LCMXFILES)  $(RCMXFILES)  $(FCMXFILES)

# Instructions to make
.PHONY: all clean depend
#.PRECIOUS: $(CMIFILES) $(CMOFILES) $(CMXFILES)\
#	$(ZSIFILES) $(ZIFILES) $(ZOFILES) $(ZXFILES)\
#	$(MLFILES) $(MLIFILES)
.SUFFIXES: .cma .cmx .cmo .cmi .zsi .zo .zi .zx\
	.ml .mli .mll .mly .prl .prli .prll .prly

# Make the library
all: $(NAME).zo $(NAME).zofiles $(ZSIFILES)

# How to make the library
$(NAME).cma: $(PCMOFILES) $(LCMOFILES)
	$(CSLC) $(CSLCFLAGS) -a -o $@ $(PCMOFILES) $(LCMOFILES)

$(NAME).cslrun: $(NAME).cma $(RCMOFILES) $(CSLLIBS)
	$(CSLC) $(CSLCFLAGS) -o $@ $(CSLLIBS) $(NAME).cma $(RCMOFILES)

$(NAME): $(CMXFILES)
	$(CSLOPT) $(CSLCFLAGS) -o $@ $(CMXFILES)

$(NAME).zo: $(LZOFILES)
	$(CAMLLIBR) -o $@ $(PZOFILES) $(LZOFILES)

$(NAME).run: $(NAME).zo $(RZOFILES) $(CAMLLIBS)
	$(CAMLC) $(CAMLCFLAGS) -o $@ $(CAMLLIBS) $(NAME).zo $(RZOFILES)

$(NAME).zofiles: Makefile
	echo "ITT_ZOFILES = $(LZOFILES)" > $@

%.zo: %.ml %.zi
	$(CAMLC) $(CAMLCFLAGS) -c $*.ml

%.zi: %.mli
	$(CAMLC) $(CAMLCFLAGS) -c $*.mli

%.zx: %.ml $.mli
	$(CAMLOPT) $(CAMLOPTFLAGS) -c $*.ml

%.cmo: %.ml %.cmi
	$(CSLC) $(CSLCFLAGS) -c $*.ml

%.cmi: %.mli
	$(CSLC) $(CSLCFLAGS) -c $*.mli

%.cmx: %.ml $.mli
	$(CSLOPT) $(CSLOPTFLAGS) -c $*.ml

%.ml: %.mll
	$(CSLLEX) $*.mll

%.ml: %.mly
	$(CSLYACC) $*.mly

%.ml: %.prl %.zsi
	$(PRLC) $(PRLCFLAGS) $*.prl

%.zsi %.mli: %.prli
	$(PRLC) $(PRLCFLAGS) $*.prli

%.mll: %.prll
	$(PRLC) $(PRLCFLAGS) $*.prll

%.mly: %.prly
	$(PRLC) $(PRLCFLAGS) $*.prly

#$(ZSIFILES) $(MLFILES) $(MLIFILES): $(PRLC.RUN)

# Other commands
README.uue: README.doc
	uuencode README.doc < README.doc > README.uue

clean:
	del -f *.cm[aiox] *.z* *~ *.ml *.ml[ily]
	del -f $(NAME) *.*run

depend: $(PRLFILES) $(PRLIFILES) $(MLFILES) $(MLIFILES)
	$(CAMLDEP) $(INCLUDE) $(PRLIFILES) $(PRLFILES) $(MLFILES) $(MLIFILES) > Makefile.dep

include Makefile.dep
