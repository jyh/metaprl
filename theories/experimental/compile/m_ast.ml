doc <:doc< 
   @begin[doc]
   This file defines the terms needed to represent the M AST.
   The language is a superset of the M IR. So far, the only
   extension is tuples, which are used to encode function
   arguments.
  
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   Copyright (C) 2003 Adam Granicz, Caltech
  
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
  
   Author: Adam Granicz
   @email{granicz@cs.caltech.edu}
   @end[license]
>>

doc <:doc< 
   @begin[doc]
   @parents
   @end[doc]
>>
extends M_util
extends M_ir
doc <:doc< @docoff >>

open Refiner.Refiner.Term
open Refiner.Refiner.TermOp

doc <:doc< 
   @begin[doc]
   We define our own tuple terms.
   @end[doc]
>>
declare mnil
declare mcons{'e; 'list}

(************************************************************************
 * Display forms
 *)

(* Our own tuples *)
dform mnil_df : mnil =
   `""
dform mcons_df1 : except_mode[src] :: mcons{'a; mcons{'b; 'c}} =
   pushm[0] `"[" slot{'a}`"," slot{'b} slot{'c} `"]" popm

dform mcons_df2 : except_mode[src] :: mcons{'a; 'b} =
   pushm[0] `"[" slot{'a} slot{'b} `"]" popm

