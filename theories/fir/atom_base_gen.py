#!/usr/bin/python2

# This script is intended to automate the process of generating
# all the rewrites needed to determine the argument and result
# types of the FIR unary and binary operators.

# BUG: The documentation in this script is a bit lacking.
# But it is pretty straightforward, and mfir_tr_atom_base.spec
# explains (briefly) the input format the script expects.

from string     import *
from xreadlines import *


# Global flags and variables.

sig_file_name = 'mfir_tr_atom_base.mli'
def_file_name = 'mfir_tr_atom_base.ml'
input         = 'mfir_tr_atom_base.spec'


#--------------------------------------------------------------------------
# General output functions.
#--------------------------------------------------------------------------

#
# Output the header for the signature file.
#

def get_sig_file_header():
   return """(*
 * The Mfir_tr_atom_base module defines the argument types
 * and result types of the FIR operators.
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent

open Tactic_type.Conversionals


(**************************************************************************
 * Declarations.
 **************************************************************************)

declare res_type{ 'op }
declare arg1_type{ 'op }
declare arg2_type{ 'op }


(**************************************************************************
 * Rewrites.
 **************************************************************************)"""


#
# Output the header for the implementation file.
#

def get_def_file_header():
   return """(*!
 * @begin[doc]
 * @module[Mfir_tr_atom_base]
 *
 * The @tt[Mfir_tr_atom_base] module defines the argument types
 * and result types of the FIR operators.
 * @end[doc]
 *
 * ------------------------------------------------------------------------
 *
 * @begin[license]
 * This file is part of MetaPRL, a modular, higher order
 * logical framework that provides a logical programming
 * environment for OCaml and other languages.  Additional
 * information about the system is available at
 * http://www.metaprl.org/
 *
 * Copyright (C) 2002 Brian Emre Aydemir, Caltech
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * Author: Brian Emre Aydemir
 * @email{emre@cs.caltech.edu}
 * @end[license]
 *)

(*!
 * @begin[doc]
 * @parents
 * @end[doc]
 *)

extends Mfir_ty
extends Mfir_exp
extends Mfir_sequent


(**************************************************************************
 * Declarations.
 **************************************************************************)

(*!
 * @begin[doc]
 * @terms
 *
 * The term @tt[res_type] returns the result type of an operator @tt[op].
 * The terms @tt[arg1_type] and @tt[arg2_type] return the types of
 * first and second arguments of an operator @tt[op] (@tt[arg2_type] is
 * undefined if @tt[op] is a unary operator).
 * @end[doc]
 *)

declare res_type{ 'op }
declare arg1_type{ 'op }
declare arg2_type{ 'op }

(*!
 * @docoff
 *)


(**************************************************************************
 * Display forms.
 **************************************************************************)

dform res_type_df : except_mode[src] ::
   res_type{ 'op } =
   bf["res_type"] `"(" slot{'op} `")"

dform arg1_type_df : except_mode[src] ::
   arg1_type{ 'op } =
   bf["arg1_type"] `"(" slot{'op} `")"

dform arg2_type_df : except_mode[src] ::
   arg2_type{ 'op } =
   bf["arg2_type"] `"(" slot{'op} `")"


(**************************************************************************
 * Rewrites.
 **************************************************************************)

(*!
 * @begin[doc]
 * @rewrites
 *
 * Rewrites are used to define the argument and result types of the
 * FIR unary and binary operators.  The types may not be well-formed
 * if the original operator is not well-formed.  We omit an explicit
 * listing of these rewrites.
 * @end[doc]
 *)

(*!
 * @docoff
 *)"""


#--------------------------------------------------------------------------
# Process a specification line.
#--------------------------------------------------------------------------

# WARNING: Do not change the output of this function significantly.

def process_line( line, sig_file, def_file ):

   # Get the basic parts out first.

   pieces = split( line, '/' )
   name = strip( pieces[0] )
   op = strip( pieces[1] )
   count = strip( pieces[2] )
   res = strip( pieces[3] )
   arg1 = strip( pieces[4] )

   if count == '2':
      arg2 = strip( pieces[5] )

   # Generate output for the signature file.

   sig_file.write( '\n\ntopval reduce_res_type_' + name + ' : conv' + \
                   '\ntopval reduce_arg1_type_' + name + ' : conv' )

   if count == '2':
      sig_file.write( '\ntopval reduce_arg2_type_' + name + ' : conv' )

   # Generate output for the implementation file.

   def_file.write( '\n\nprim_rw reduce_res_type_' + name + ' :' + \
                   '\n   res_type{ ' + op + ' } <-->' + \
                   '\n   ' + res + \
                   '\n\nprim_rw reduce_arg1_type_' + name + ' :' + \
                   '\n   arg1_type{ ' + op + ' } <-->' + \
                   '\n   ' + arg1 )

   if count == '2':
      def_file.write( '\n\nprim_rw reduce_arg2_type_' + name + ' :' + \
                      '\n   arg2_type { ' + op + ' } <-->' + \
                      '\n   ' + arg2 )

   def_file.write( '\n\nlet resource reduce += [' + \
                   '\n   << res_type{ ' + op + ' } >>, ' + \
                   'reduce_res_type_' + name + ';' + \
                   '\n   << arg1_type{ ' + op + ' } >>, ' + \
                   'reduce_arg1_type_' + name + ';' )

   if count == '2' :
      def_file.write( '\n   << arg2_type{ ' + op + ' } >>, ' + \
                      'reduce_arg2_type_' + name + ';' )

   def_file.write( '\n]\n' )


#--------------------------------------------------------------------------
# Process input and generate output.
#--------------------------------------------------------------------------

# Open files for output.

sig_file = open( sig_file_name, 'w' )
def_file = open( def_file_name, 'w' )


# Print headers to files.

sig_file.write( get_sig_file_header() )
def_file.write( get_def_file_header() )


# Process input.

input_file = open( input, 'r' )

for line in xreadlines( input_file ):
   if line == '\n':
      pass
   elif line[0] == '#':
      pass
   else:
      process_line( line, sig_file, def_file )


# Close files and exit

sig_file.close()
def_file.close()
input_file.close()

print 'Sig file output: ' + sig_file_name
print 'Def file output: ' + def_file_name
