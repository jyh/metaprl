#
# No special includes
#
INCLUDE := -I $(NLLIB)
OCAMLDEPFLAGS := -prl

# Types files
MLZFILES :=\
	tactic_type

# Library files
NLFILES :=\
	tactic_cache\
	tactic_type\
	sequent\
	tacticals\
	var\
	options

# Name of main libraris
MAIN = tactics

all: $(MAIN).cma
opt: $(MAIN).cmxa
install:: all

clean::
	$(RM) -f *.p4* *.pp*

# Real makefile
include ../../mk/config
include Makefile.dep
