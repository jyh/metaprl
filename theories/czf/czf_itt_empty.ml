doc <:doc<
   @module[Czf_itt_empty]

   The @tt{Czf_itt_empty} module defines an empty set
   as the set $@collect{x; <<void>>; x}$.  Since the <<void>>
   type is empty, the set has no elements.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998 Jason Hickey, Cornell University

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
   @email{jyh@cs.cornell.edu}
   @end[license]
>>

doc <:doc< @parents >>
extends Czf_itt_member
doc docoff

open Lm_debug
open Lm_printf

open Dtactic

(************************************************************************
 * TERMS                                                                *
 ************************************************************************)

doc terms
declare "empty"

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

doc <:doc<
   @rewrites

   The empty set uses the empty index type <<void>>.
>>
prim_rw unfold_empty : empty <--> collect{void; x. 'x}
doc docoff

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform empty_df : empty =
   `"{}"

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules

   There are only two rules for the empty set: it is
   a well-formed set, and it has no elements.
>>
interactive empty_isset {| intro [] |} :
   sequent { <H> >- isset{empty} }

(*
 * Nothing is in the empty set.
 *)
interactive empty_member_elim {| elim [] |} 'H :
   sequent { <H>; x: mem{'y; empty}; <J['x]> >- 'T['x] }
doc docoff

(*
 * -*-
 * Local Variables:
 * Caml-master: "editor.run"
 * End:
 * -*-
 *)
