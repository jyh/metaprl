doc <:doc< 
   @begin[doc]
   @module[Mfir_record]
  
   The @tt[Mfir_record] module defines a syntactic mechanism for
   representing records and operations on records.
   @end[doc]
  
   ------------------------------------------------------------------------
  
   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.  Additional
   information about the system is available at
   http://www.metaprl.org/
  
   Copyright (C) 2002 Brian Emre Aydemir, Caltech
  
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License
   as published by the Free Software Foundation; either version 2
   of the License, or (at your option) any later version.
  
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
  
   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
  
   Author: Brian Emre Aydemir
   @email{emre@cs.caltech.edu}
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>

extends Mfir_bool
extends Mfir_token

doc <:doc< 
   @docoff
>>

open Top_conversionals
open Mfir_bool
open Mfir_token


(**************************************************************************
 * Declarations.
 **************************************************************************)

doc <:doc< 
   @begin[doc]
   @terms
  
   Records are used to represent maps from labels to values.
   The term @tt[recordEnd] is an empty record.  The term  @tt[record]
   is a record that binds the label @tt[tag] to the value @tt[data].
   The subterm @tt[remaining] is the remainder of the record.
   @end[doc]
>>

declare recordEnd
declare record[tag:s]{ 'data; 'remaining }


doc <:doc< 
   @begin[doc]
  
   The term @tt[field] is used to retrieve the data from the field
   labelled @tt[tag] in the given record.  The term @tt[field_mem]
   tests if there is a binding for @tt[tag] in the given record.
   @end[doc]
>>

declare field[tag:s]{ 'record }
declare field_mem[tag:s]{ 'record }

doc <:doc< 
   @docoff
>>


(**************************************************************************
 * Rewrites.
 **************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
  
   Reducing a field operation is straightforward.
   @end[doc]
>>

prim_rw reduce_field_main :
   field[tag1:s]{ record[tag2:s]{ 'data; 'remaining } } <-->
   (if token_eq{ token[tag1:s]; token[tag2:s] } then
      'data
   else
      field[tag1:s]{ 'remaining })

doc <:doc< 
   @docoff
>>

let reduce_field =
   reduce_field_main thenC
   (addrC [0] reduce_token_eq) thenC
   reduce_ifthenelse

let resource reduce +=
   << field[tag1:s]{ record[tag2:s]{ 'data; 'remaining } } >>,
      reduce_field

doc <:doc< 
   @begin[doc]
  
   Determining whether or not a label is bound in a record is straightforward.
   @end[doc]
>>

prim_rw reduce_field_mem_base :
   field_mem[tag:s]{ recordEnd } <-->
   "false"

prim_rw reduce_field_mem_ind :
   field_mem[tag1:s]{ record[tag2:s]{ 'data; 'remaining } } <-->
   "or"{ token_eq{ token[tag1:s]; token[tag2:s] };
         field_mem[tag1:s]{ 'remaining } }

doc <:doc< 
   @docoff
>>

let reduce_field_mem =
   reduce_field_mem_base orelseC
   (  reduce_field_mem_ind thenC
      (addrC [0] reduce_token_eq) thenC
      reduce_or thenC
      reduce_ifthenelse
   )

let resource reduce +=
   << field_mem[tag:s]{ 'record } >>,
      reduce_field_mem

(**************************************************************************
 * Display forms.
 **************************************************************************)

(*
 * Use an auxiliary term to come up with a nicer display form.
 *)

declare mfir_record_display{ 'record }

(*
 * Define the display forms now.
 *)

dform recordEnd_df : except_mode[src] ::
   recordEnd =
   `"{}"

dform record_df : except_mode[src] ::
   record[tag:s]{ 'data; 'remaining } =
   `"{" mfir_record_display{ record[tag:s]{ 'data; 'remaining } } `"}"

dform mfir_record_display_df1 : except_mode[src] ::
   mfir_record_display{ 't } =
   slot{'t}

dform mfir_record_display_df2 : except_mode[src] ::
   mfir_record_display{ record[tag:s]{ 'data; 'remaining } } =
   slot[tag:s] `":" slot{'data} `";" mfir_record_display{ 'remaining }

dform mfir_record_display_df3 : except_mode[src] ::
   mfir_record_display{ recordEnd } =
   `""

dform field_df : except_mode[src] ::
   field[tag:s]{ 'record } =
   bf["field"] `"[" slot[tag:s] `"](" slot{'record} `")"

dform field_mem_df : except_mode[src] ::
   field_mem[tag:s]{ 'record } =
   bf["field_mem"] `"[" slot[tag:s] `"](" slot{'record} `")"
