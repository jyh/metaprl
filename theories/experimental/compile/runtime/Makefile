ASMFILES = x86_glue.s
CFILES   = x86_runtime.c
OFILES   = x86_glue.o x86_runtime.o

CFLAGS   = -Wall -g

LIB = libruntime.a

$(LIB): $(OFILES) Makefile
	rm -f $@
	ar cr $@ $(OFILES)
	ranlib $@
