#!/bin/sh

# If you want to add a new variable to this file (mk/make_config.sh),
# make sure you add a default value to mk/preface
# and add this value to the mk/config target in the top-level Makefile

if [ "$ENSROOT"x = x -o ! -d "$ENSROOT" ]; then
   ENSROOT=undefined
fi
if [ "$OCAMLSRC"x = x -o ! -d "$OCAMLSRC" ]; then
   OCAMLSRC=undefined
fi

if [ -f $ROOT/mk/config ]; then
   mv -f $ROOT/mk/config $ROOT/mk/config.old
   CONFIG_EXISTED=yes
fi

cat > $ROOT/mk/config << end_of_cat
# Main MetaPRL configuration file.

# This file (mk/config) is generated by make using mk/make_config.sh
# If you want to change anything except for the variable values,
# put it into mk/config.local or edit mk/make_config.sh.

# Term module to use: ds or std
# See doc/htmlman/developer-guide/term_modules.html or
# http://cvs.metaprl.org:12000/metaprl/developer-guide/term_modules.html
# for more information.
# If not sure, use ds
#
TERMS=$TERMS

#
# What representation to use for hypothesis and conclusion lists
# Possible values: Array, Splay (for splay trees)
# If not sure, use Array
#
SEQ_SET=$SEQ_SET

#
# Refiner verbosity: VERBOSE or SIMPLE
# See doc/htmlman/developer-guide/refiner_verb_and_simp.html or
# http://cvs.metaprl.org:12000/metaprl/developer-guide/refiner_verb_and_simp.html
# for more information.
# If not sure, use VERBOSE
#
REFINER=$REFINER

#
# This is the list of theory directories theory/*
# that you want to compile.  You want to include at least
#    THEORIES = base
# Include itt if you want to use the Nuprl type theory,
# and add any additional theory directories after that.
#
# Alternatively, use THEORIES = all, or THEORIES = default
#
THEORIES=$THEORIES

#
# Use GNU readline package (available on Linux at least) (yes/no).
#
READLINE=$READLINE

#
# The GNU ncurses package (available in Linix at least) (yes/no)
#
NCURSES=$NCURSES

#
# C compiler
#
CCC=$CCC

#
# Extra make options
#
MAKE_OPTS=$MAKE_OPTS

#
# Whether to compile in various test theories and files (yes/no)
#
TESTS=$TESTS

#
# If LIBMOJAVE is defined, it should point
# to the directory where you have a copy of the lm_libmojave
# (http://mojave.metaprl.org/cgi-bin/viewcvs.cgi/mcc/lm_libmojave/)
#
LIBMOJAVE=$LIBMOJAVE

#
# If ENSROOT is defined, it should point
# to the root of the Ensemble source tree
# In this case Ensemble support would be compiled into Meta-PRL
#
ENSROOT=$ENSROOT

#
# If OCAMLSRC is defined, it should point
# to the root of the OCaml source tree
# In this case Jason's marshaller debugging code
# would be compiled into Meta-PRL
# Do not enable this unless you know what you are doing!
#
OCAMLSRC=$OCAMLSRC

#
# Do you want to use sloppy dependencies?  If enabled, then updating
# the refiner will not force theory files to be reomcpiled.  If
# in doubt, you showld use "false".
#
SLOPPY_DEPENDENCIES=$SLOPPY_DEPENDENCIES

# This file (mk/config) is generated by make using mk/make_config.sh
# If you want to change anything except for the variable values,
# put it into mk/config.local or edit mk/make_config.sh.

end_of_cat

if [ "$CONFIG_EXISTED" != "yes" ]; then
   cat << end_of_cat

A new config file mk/config was created for you.

You should edit it before contunuing.

end_of_cat
   exit 1
fi
