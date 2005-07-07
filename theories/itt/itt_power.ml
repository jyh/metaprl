doc <:doc<
   @module[Itt_power]

   A power of a type <<'T>> is a type of all @i{subsets} of <<'T>>.


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

   Authors:
    Alexei Kopylov @email{kopylov@cs.caltech.edu}

   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_subset

doc docoff

open Basic_tactics


doc <:doc<
   @modsection{Definition}
>>

define unfold_Power: Power[i:l]{'T} <--> {X : univ[i:l] | 'X subset 'T}

dform power_df :  Power[i:l]{'T} = `"P" sub[i:l] `"(" slot{'T} `")"

(* Question: Should this type be quotient by ext_equal?
   In theory it should, but then the usual operators would not have the intended types.
   For example, membership, subtyping and other relations would not be propositions
   anymore (one would have to use esquash on them).
   The same problem is with the definition: prop = univ // <==>. We would like to
   have this type, but in practice it's only a headache.
   Ideally, we should have:
     univ[i]
     type[i] = univ[i] // ext_equal
     prop[i] = univ[i] // <==>
   Then squash : prop -> univ, esquash : type -> univ.
   This would be practical only if, we allow to have propositions in sequents.
   But then the rule "A |- A Type" would be invalid.
                                                                   AK
*)

doc <:doc<
   @modsection{Basic Rules}
>>

interactive power_wf {| intro[] |} :
   sequent{ <H> >- "type"{'T} } -->
   sequent{ <H> >- "type"{Power[i:l]{'T}} }

interactive power_eq {| intro[] |} :
   sequent{ <H> >- cumulativity[i:l,j:l] } -->
   sequent{ <H> >- 'T_1 = 'T_2 in univ[j:l] } -->
   sequent{ <H> >- Power[i:l]{'T_1} = Power[i:l]{'T_2} in univ[j:l] }

interactive power_intro {| intro[AutoMustComplete] |} :
   sequent{ <H> >- 'X subset 'T } -->
   sequent{ <H> >- 'X in univ[i:l] } -->
   sequent{ <H> >- 'X in Power[i:l]{'T} }

interactive power_elimination {| elim [] |} 'H :
   sequent { <H>; X: univ[i:l];  'X subset 'T; <J['X]> >- 'C['X] } -->
   sequent { <H>; X: Power[i:l]{'T} ; <J['X]> >- 'C['X] }

(* TODO: We need also no-thinnig version of elim *)

interactive power_univ {| intro[intro_typeinf <<'X>>] |}  Power[i:l]{'T}:
   sequent{ <H> >- 'X in Power[i:l]{'T} } -->
   sequent{ <H> >- 'X in univ[i:l] }

interactive power_type {| intro[intro_typeinf <<'X>>] |}  Power[i:l]{'T}:
   sequent{ <H> >- 'X in Power[i:l]{'T} } -->
   sequent{ <H> >- "type"{'X} }

doc <:doc<
   @modsection{Trivia}
>>


interactive power_triv1 {| elim []  |} 'H :
   sequent { <H>; X: Power[i:l]{'T} ; <J['X]> >- univ[i:l] subtype univ[j:l] } -->
   sequent { <H>; X: Power[i:l]{'T} ; <J['X]> >- 'X in univ[j:l] }

interactive power_triv2 {| nth_hyp  |} 'H :
   sequent { <H>; X: Power[i:l]{'T} ; <J['X]> >- "type"{'X} }

interactive power_triv3 {| nth_hyp |} 'H :
   sequent { <H>; X: Power[i:l]{'T} ; <J['X]> >- 'X subset 'T }

interactive power_triv4 {| nth_hyp |} 'H :
   sequent { <H>; X: Power[i:l]{'T} ; <J['X]> >- 'X subtype 'T }



(* TODO: Power{T} is closed under isect, union, and complement to T.
   Of course empty set is always in P(T) *)
(* More TODO: Power{T} forms lattice *)


