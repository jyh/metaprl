doc <:doc< 
   @begin[doc]
   @module[Czf_itt_pair]
  
   The @tt{Czf_itt_pair} module defines the binary pairing
   constructor $@pair{s_1; s_2}$.  The pair is derived from
   the union and singleton.
  
   $$@pair{s_1; s_2} @equiv @union{@sing{s_1}; @sing{s_2}}$$
  
   The pair has two elements: the set $s_1$ and the set $s_2$.
   @end[doc]
  
   ----------------------------------------------------------------
  
   @begin[license]
   Copyright (C) 2000 Jason Hickey, Caltech
  
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
>>

doc <:doc< @doc{@parents} >>
extends Czf_itt_union
extends Czf_itt_singleton
doc <:doc< @docoff >>

open Dtactic

(************************************************************************
 * TERMS
 ************************************************************************)

doc <:doc< @doc{@terms} >>
declare pair{'s1; 's2}
doc <:doc< @docoff >>

(************************************************************************
 * REWRITES
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rewrites
   The pair is a union of two singleton sets.
   @end[doc]
>>
prim_rw unfold_pair : pair{'s1; 's2} <-->
   union{sing{'s1}; sing{'s2}}
doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform pair_df : pair{'s1; 's2} =
   `"(" pushm[0] szone slot{'s1} `"," hspace slot{'s2} `")" ezone popm

(************************************************************************
 * RULES
 ************************************************************************)

doc <:doc< 
   @begin[doc]
   @rules
   @modsubsection{Well-formedness}
  
   The pair is a set if both arguments are sets.
   @end[doc]
>>
interactive pair_isset {| intro [] |} :
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- isset{pair{'s1; 's2}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Introduction}
  
   The elements of the pair $@pair{s_1; s_2}$ are the
   sets $s_1$ and $s_2$.
   @end[doc]
>>
interactive pair_member_intro_left {| intro [SelectOption 1] |} :
   ["wf"] sequent { <H> >- isset{'x} } -->
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- eq{'x; 's1} } -->
   sequent { <H> >- mem{'x; pair{'s1; 's2}} }

interactive pair_member_intro_right {| intro [SelectOption 2] |} :
   ["wf"] sequent { <H> >- isset{'x} } -->
   ["wf"] sequent { <H> >- isset{'s1} } -->
   ["wf"] sequent { <H> >- isset{'s2} } -->
   sequent { <H> >- eq{'x; 's2} } -->
   sequent { <H> >- mem{'x; pair{'s1; 's2}} }

doc <:doc< 
   @begin[doc]
   @modsubsection{Elimination}
  
   The @emph{only} elements of the pair $@pair{s_1; s_2}$ are
   the sets $s_1$ and $s_2$.
   @end[doc]
>>
interactive pair_member_elim {| elim [] |} 'H :
   ["wf"] sequent { <H>; x: mem{'y; pair{'s1; 's2}}; <J['x]> >- isset{'y} } -->
   ["wf"] sequent { <H>; x: mem{'y; pair{'s1; 's2}}; <J['x]> >- isset{'s1} } -->
   ["wf"] sequent { <H>; x: mem{'y; pair{'s1; 's2}}; <J['x]> >- isset{'s2} } -->
   sequent { <H>; x: mem{'y; pair{'s1; 's2}}; <J['x]>; z: eq{'y; 's1} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; pair{'s1; 's2}}; <J['x]>; z: eq{'y; 's2} >- 'T['x] } -->
   sequent { <H>; x: mem{'y; pair{'s1; 's2}}; <J['x]> >- 'T['x] }

doc <:doc< 
   @begin[doc]
   @modsubsection{Functionality}
  
   The pair is functional in both its arguments.
   @end[doc]
>>
interactive pair_fun {| intro [] |} :
   sequent { <H> >- fun_set{z. 's1['z]} } -->
   sequent { <H> >- fun_set{z. 's2['z]} } -->
   sequent { <H> >- fun_set{z. pair{'s1['z]; 's2['z]}} }
doc <:doc< @docoff >>

(*
 * -*-
 * Local Variables:
 * Caml-master: "compile"
 * End:
 * -*-
 *)
