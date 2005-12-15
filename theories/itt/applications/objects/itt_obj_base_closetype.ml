doc <:doc<
   @module[Itt_object_base_closetype]


   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

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

   Author: Alexei Kopylov
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_union_of
extends Itt_subtype
extends Itt_dfun
extends Itt_record
extends Itt_monotone_subtyping
extends Itt_obj_base_rewrite

doc <:doc< @docoff >>

open Basic_tactics

open Itt_tunion


(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc<
   @terms

>>

define unfold_Obj: Obj[l:l]{Self.'M['Self]} <--> union_of{{X:univ[l:l] | 'X subtype 'X -> 'M['X]}}

doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform obj_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: Obj[l:l]{Self.'M} =
   `"Obj" sub[l:l] `" " slot{'Self} `"." slot{'M}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)


doc <:doc<
   @rules
   @modsubsection{Typehood and equality}
>>
interactive objEquality {| intro [] |} :
   [wf] sequent { <H> >- cumulativity[l:l, i:l] } -->
   [wf] sequent { <H>; Self:univ[l:l] >- 'M_1['Self]='M_2['Self] in univ[i:l] } -->
   sequent { <H> >- Obj[l:l]{Self.'M_1['Self]} =  Obj[l:l]{Self.'M_2['Self]} in univ[i:l] }

interactive objType {| intro [] |} :
   [wf] sequent { <H>; Self:univ[l:l] >- "type"{'M['Self]} } -->
   sequent { <H> >- "type"{  Obj[l:l]{Self.'M['Self]}  } }

doc <:doc<
   @modsubsection{Membership}
   No simple rule for membership.
>>

doc <:doc<
   @modsubsection{Elimination}
>>

(*
interactive objElimination {| elim [] |} :
   sequent { <H> >- 'obj in Obj[l:l]{Self.'M['Self]}  } -->
   sequent { <H> >- 'obj 'obj in 'M[Obj[l:l]{Self.'M['Self]}]  }

*)

interactive objElimination {| elim [] |} 'H :
   [wf] sequent { <H>; obj: Obj[l:l]{Self.'M['Self]}; <J['obj]>  >- monotone[l':l]{X.'M['X]} } -->
   sequent { <H>; obj: Obj[l:l]{Self.'M['Self]}; <J['obj]>; 'obj 'obj in 'M[Obj[l:l]{Self.'M['Self]}]  >- 'C['obj]  } -->
   sequent { <H>; obj: Obj[l:l]{Self.'M['Self]}; <J['obj]> >- 'C['obj]  }


interactive apply_object_wf {| intro[AutoMustComplete; intro_typeinf<<'obj>> ] |} <<Obj[l:l]{X.'X -> 'M['X]}>> :
   sequent{ <H> >- monotone[l':l]{X.'M['X]} } -->
   sequent{ <H> >- 'obj in  Obj[l:l]{Self.'M['Self]}  } -->
   sequent{ <H> >- 'M[ Obj[l:l]{Self.'M['Self]} ] subtype record[m:t]{'A} } -->
   sequent{ <H> >- apply[m:t]{'obj} in 'A }



doc <:doc<
   @modsubsection{Subtyping}
>>



doc <:doc< @docoff >>

(************************************************************************
 * TACTICS                                                              *
 ************************************************************************)

(*
 * -*-
 * Local Variables:
 * Caml-master: "nl"
 * End:
 * -*-
 *)
