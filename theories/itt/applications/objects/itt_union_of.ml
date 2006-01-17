doc <:doc<
   @module[Itt_union_of]

   The @tt[Itt_union_of] module defines a union of all types in a type.

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
extends Itt_tunion
doc <:doc< @docoff >>

open Basic_tactics

open Itt_tunion

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc<
   @terms

   The @tt{tunion} term defines the union type.
>>

define union_of : union_of{'T} <--> tunion{'T; X.'X}

doc <:doc< @docoff >>

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

dform union_of_df : except_mode[src] :: parens :: "prec"[prec_tunion] :: union_of{'T} =
   cup slot{'T}

(************************************************************************
 * RULES                                                                *
 ************************************************************************)


doc <:doc<
   @rules
   @modsubsection{Typehood and equality}
>>
interactive union_ofEquality {| intro [] |} :
   [wf] sequent { <H> >- 'T_1 = 'T_2 in univ[i:l] } -->
   [wf] sequent { <H>; X:'T_1 >- 'X in univ[i:l] } -->
   sequent { <H> >- union_of{'T_1} = union_of{'T_2} in univ[i:l] }

interactive union_ofType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'T} } -->
   [wf] sequent { <H>; X:'T >- "type"{'X} } -->
   sequent { <H> >- "type"{ union_of{'T} } }

doc <:doc<
   @modsubsection{Membership}
>>
interactive union_ofMemberEquality {| intro [AutoMustComplete; intro_typeinf <<'x1>>] |} 'A :
   [wf] sequent { <H>; X:'T >- "type"{'X} } -->
   sequent { <H> >- 'A in 'T } -->
   sequent { <H> >- 'x1 = 'x2 in 'A } -->
   sequent { <H> >- 'x1 = 'x2 in union_of{'T}  }

doc <:doc<
   @modsubsection{Introduction}
>>
interactive union_ofIntroduction {| intro [] |} 'A :
   [wf] sequent { <H>; X:'T >- "type"{'X} } -->
   sequent { <H> >- 'A in 'T } -->
   sequent { <H> >- 'A } -->
   sequent { <H> >- union_of{'T}  }


doc <:doc<
   @modsubsection{Elimination}
>>

let union_ofElimT n = rwh union_of n thenT dT n
let resource elim += (<< union_of{'T} >>, wrap_elim union_ofElimT)

doc <:doc<
   @modsubsection{Subtyping}
>>

interactive union_ofSubtype {| intro [AutoMustComplete] |}:
   [wf] sequent { <H>; X:'T >- "type"{'X} } -->
   sequent { <H> >- 'X in 'T } -->
   sequent { <H> >- 'X subtype union_of{'T}  }


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
