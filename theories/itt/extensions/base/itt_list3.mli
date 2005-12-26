doc <:doc<
   More list operations.

   ----------------------------------------------------------------

   @begin[license]
   Copyright (C) 2005 Mojave Group, Caltech

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

   Author: Jason Hickey
   @email{jyh@cs.caltech.edu}
   @end[license]

   @parents
>>
extends Itt_list2

open Basic_tactics

(*
 * Prefix and suffix operations.
 *)
declare nth_prefix{'l; 'i}
declare nth_suffix{'l; 'i}

(************************************************************************
 * Tactics.
 *)
resource (term * conv, conv) normalize_list_of_fun

val process_normalize_list_of_fun_resource_rw_annotation : (prim_rewrite, term * conv) rw_annotation_processor

topval normalizeListOfFunTopC : conv
topval normalizeListOfFunC : conv
topval normalizeListOfFunT : tactic

(*!
 * @docoff
 *
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
