#!/usr/bin/python2

# This script extracts term declarations from a file and generates
# signatures and functions to construct and deconstruct those terms.
# It is not a general purpose script; assumptions about file names,
# format of the input files, etc. are all hardcoded, though
# some of these assumptions are easier to change than others.

# BUG: This script is horribly documented.  Don't be surprised
# if it's hard to figure out or maintain.

# BUG: I'm assuming that terms, if they have any subterms with bound
# variables, have exactly one such subterm, and that it is the last subterm.

from string     import *
from xreadlines import *

# Global flags and variables.

sig_file_name = 'mfir_termOp.mli'
def_file_name = 'mfir_termOp.ml'
inputs        = [ 'mfir_bool.mli',
                  'mfir_int.mli',
                  'mfir_list.mli',
                  'mfir_int_set.mli',
                  'mfir_ty.mli',
                  'mfir_exp.mli' ]

###########################################################################
# Output functions.
###########################################################################

#
# Output generic header.
#

def get_header():
   return """(*
 * The Mfir_termOp module provides term construction
 * and deconstruction terms for FIR theory terms.
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
 *)"""

#
# Make strings out of data.
#

def mk_sig_of_data( pdata, sdata ):

   ans = ''

   for i in pdata:
      if i == 'n':
         ans = ans + 'Mp_num.num -> '
      elif i == 's':
         ans = ans + 'string -> '

   (subterms, bterms) = sdata

   if bterms == 0:
      for i in range(subterms):
         ans = ans + 'term -> '
   else:
      for i in range(subterms-1):
         ans = ans + 'term -> '
      for i in range(bterms):
         ans = ans + 'string -> '
      ans = ans + 'term -> '

   return ans + 'term'

def dest_sig_of_data( pdata, sdata ):

   ans = ''

   for i in pdata:
      if i == 'n':
         ans = ans + 'Mp_num.num * '
      elif i == 's':
         ans = ans + 'string * '

   (subterms, bterms) = sdata

   if bterms == 0:
      for i in range(subterms):
         ans = ans + 'term * '
   else:
      for i in range(subterms-1):
         ans = ans + 'term * '
      for i in range(bterms):
         ans = ans + 'string * '
      ans = ans + 'term * '

   return ('term -> ' + ans)[:-3]

def tag_of_data( pdata, sdata ):

   ans = ''

   for i in pdata:
      if i == 'n':
         ans = ans + 'num_'
      elif i == 's':
         ans = ans + 'str_'

   (subterms, bterms) = sdata

   if bterms == 0:
      ans = ans + repr(subterms) + '_dep0_'
   else:
      ans = ans + repr(subterms-1) + '_dep0_1_dep' + repr(bterms) + '_'

   return ans

#
# Generate output for given term.
# WARNING: Do not change the output of this function significantly.
#

def output_line( full_term, term_name, pdata, sdata, sig_file, def_file ):

   tag = tag_of_data( pdata, sdata )

   # Output for any sort of term

   sig_file.write( '\n\n' + \
                   'val ' + term_name + '_term : term\n' + \
                   'val is_' + term_name + '_term : term -> bool' )

   def_file.write( '\n\n' + \
                   'let ' + term_name + '_term = ' + \
                   '<< ' + full_term + ' >>\n' + \
                   'let ' + term_name + '_opname = opname_of_term ' + \
                   term_name + '_term\n' + \
                   'let is_' + term_name + '_term = is_' + \
                   tag + 'term ' + term_name + '_opname' )

   # Output dependent on ``kind'' of term.

   if (pdata != []) or (sdata != (0, 0)):

      mk_sig = mk_sig_of_data( pdata, sdata )
      dest_sig = dest_sig_of_data( pdata, sdata )

      sig_file.write( '\nval mk_' + term_name + '_term : ' + mk_sig + '\n' + \
                      'val dest_' + term_name + '_term : ' + dest_sig )

      def_file.write( '\nlet mk_' + term_name + '_term = mk_' + \
                      tag + 'term ' + term_name + '_opname\n' + \
                      'let dest_' + term_name + '_term = dest_' + \
                      tag + 'term ' + term_name + '_opname' )

###########################################################################
# Process a ``declare'' line.
###########################################################################

def process_line( str, sig_file, def_file ):

   # Find basic delimeters
   curl_start = find( str, '{' )
   sq_start = find( str, '[' )
   sq_end = find( str, ']' )

   # Get the ``term name''.
   if (sq_start > 0) and (curl_start > 0):
      term_name = str[:min(sq_start,curl_start)]
   elif (sq_start < 0) and (curl_start < 0):
      term_name = str
   elif (sq_start < 0):
      term_name = str[:curl_start]
   else:
      term_name = str[:sq_start]

   if term_name[0] == '"':
      term_name = term_name[1:-1]

   # Encode the parameters
   pdata = []
   if (sq_start > 0) and ((curl_start < 0) or (sq_start < curl_start)):
      for param in split( strip( str[sq_start+1:sq_end] ), ',' ):
         pdata.append( param[-1] )

   # Encode the subterms
   sdata = (0, 0)
   if curl_start > 0:
      pieces = split( str[curl_start:], ';' )
      bterms_part = split( pieces[-1], '.' )[0]
      if bterms_part != pieces[-1]:
         sdata = ( len(pieces), len(split(bterms_part, ',')) )
      else:
         sdata = ( len(pieces), 0 )

   # Generate output
   output_line( str, term_name, pdata, sdata, sig_file, def_file )

###########################################################################
# Process files and generate output.
###########################################################################

# Open files for output.

sig_file = open( sig_file_name, 'w' )
def_file = open( def_file_name, 'w' )

# Print headers to files.

sig_file.write( get_header() )
sig_file.write( '\n\nextends Mfir_bool\n' + \
                'extends Mfir_int\n' + \
                'extends Mfir_int_set\n' + \
                'extends Mfir_list\n' + \
                'extends Mfir_ty\n' + \
                'extends Mfir_exp\n\n' + \
                'open Refiner.Refiner.Term' )

def_file.write( get_header() )
def_file.write( '\n\nextends Mfir_bool\n' + \
                'extends Mfir_int\n' + \
                'extends Mfir_int_set\n' + \
                'extends Mfir_list\n' + \
                'extends Mfir_ty\n' + \
                'extends Mfir_exp\n\n' + \
                'open Mfir_termOp_base\n' + \
                'open Refiner.Refiner.Term' )

# Process files.

for file_name in inputs:

   print '-> Processing file: ' + file_name
   input_file = open( file_name, 'r' )

   for line in xreadlines( input_file ):
      if line[0:8] == 'declare ':
         process_line( strip( line[8:] ), sig_file, def_file )

   input_file.close()

# Close files and exit

sig_file.close()
def_file.close()

print 'Sig file output: ' + sig_file_name
print 'Def file output: ' + def_file_name
