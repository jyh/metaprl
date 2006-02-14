doc <:doc<
   @module[Itt_nequal]

   The @tt[Itt_nequal] module defines non-equality term <<'a <> 'b in 'T>>.

   @docoff
   ----------------------------------------------------------------

   @begin[license]

   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 2003-2006 MetaPRL Group, Cornell University and
   California Institute of Technology

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

   Author: Alexei Kopylov
   @email{kopylov@cs.cornell.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>

extends Itt_equal
extends Itt_logic

open Basic_tactics

open Itt_equal
open Itt_struct

(************************************************************************
 * DEFINITIONS                                                          *
 ************************************************************************)

define unfold_nequal: nequal{'T; 'a; 'b} <--> not{'a='b in 'T}

(************************************************************************
 * DISPLAY FORMS                                                        *
 ************************************************************************)

dform nequal_df : except_mode[src] :: parens :: "prec"[prec_equal] :: nequal{'T; 'a; 'b} =
   szone pushm slot["le"]{'a} space neq space slot["le"]{'b} space Mpsymbols!member `" " slot["le"]{'T} popm ezone

dform nequal_df2 : mode[src] :: parens :: "prec"[prec_equal] :: nequal{'T; 'a; 'b} =
   szone pushm slot["le"]{'a} space `"<> " slot["le"]{'b} space `"in " slot["le"]{'T} popm ezone

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

interactive neq_type {| intro[] |}:
   [wf] sequent { <H> >- 'x in 'T } -->
   [wf] sequent { <H> >- 'y in 'T } -->
   sequent { <H> >- "type"{'x <> 'y in 'T} }

interactive neq_univ {| intro [] |} :
   sequent { <H> >- 'T1 = 'T2 in univ[i:l] }  -->
   sequent { <H> >- 'x1 = 'x2 in 'T1 } -->
   sequent { <H> >- 'y1 = 'y2 in 'T1 } -->
   sequent { <H> >- ('x1 <> 'y1 in 'T1)  = ('x2 <> 'y2 in 'T2 ) in univ[i:l] }


interactive neq_intro {| intro[AutoMustComplete] |}:
   [wf] sequent { <H> >- 'x in 'T } -->
   [wf] sequent { <H> >- 'y in 'T } -->
   sequent { <H>; 'x ='y in 'T >- "false" } -->
   sequent { <H> >- 'x <> 'y in 'T }

interactive neq_sym :
   [wf] sequent { <H> >- 'x in 'T } -->
   [wf] sequent { <H> >- 'y in 'T } -->
   sequent { <H> >- 'y <> 'x in 'T } -->
   sequent { <H> >- 'x <> 'y in 'T }

interactive neq_elim {| elim [ThinOption thinT] |} 'H :
   [main] sequent { <H>; u:  'x <> 'y in 'T ; <J['u]> >-  'x = 'y in 'T  } -->
   sequent { <H>; u: 'x <> 'y in 'T; <J['u]> >- 'C }

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * Automation.
 *)
let triv_nequalT = neq_sym thenLT [idT;idT; completeT trivialT]

let resource intro += <<'x <>'y in 'T>> , wrap_intro (triv_nequalT orelseT neq_intro)

