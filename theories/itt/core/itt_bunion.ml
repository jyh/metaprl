doc <:doc<
   @module[Itt_bunion]

   The @tt{Itt_bunion} module defines a binary union $@bunion{A; B}$
   of type types $A$ and $B$.  The elements include the elements of $A$
   as well as the elements of $B$.  Two elements are equal
   if they are equal in @emph{either} of the types.

   @docoff
   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/htmlman/default.html or visit http://metaprl.org/
   for more information.

   Copyright (C) 1998-2006 MetaPRL Group, Cornell University and
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

   Author: Jason Hickey @email{jyh@cs.cornell.edu}
   Modified by: Aleksey Nogin @email{nogin@cs.caltech.edu}
   @end[license]
>>

doc <:doc<
   @parents
>>
extends Itt_tunion
extends Itt_bool
extends Itt_struct
doc docoff

open Basic_tactics

open Itt_equal
open Itt_struct
open Itt_squash

(************************************************************************
 * SYNTAX                                                               *
 ************************************************************************)

doc <:doc<
   @terms

   The binary union is defined using the @hrefterm[tunion]
   over the space of Booleans.
>>
define unfold_bunion : "bunion"{'A; 'B} <-->
                          Union x: bool. ifthenelse{'x; 'A; 'B}
doc docoff

(************************************************************************
 * DISPLAY                                                              *
 ************************************************************************)

prec prec_bunion

dform bunion_df : parens :: "prec"[prec_bunion] :: except_mode[src] :: "bunion"{'A; 'B} =
   slot["le"]{'A} `" " cup space slot{'B}

(************************************************************************
 * REWRITES                                                             *
 ************************************************************************)

let fold_bunion = makeFoldC << 'A bunion 'B >> unfold_bunion

(************************************************************************
 * RULES                                                                *
 ************************************************************************)

doc <:doc<
   @rules
   @modsubsection{Typehood and equality}

   The union $@bunion{A; B}$ is well-formed if
   both $A$ and $B$ are types.
>>
interactive bunionEquality {| intro [] |} :
   [wf] sequent { <H> >- 'A1 = 'A2 in univ[i:l] } -->
   [wf] sequent { <H> >- 'B1 = 'B2 in univ[i:l] } -->
   sequent { <H> >- 'A1 bunion 'B1 = 'A2  bunion 'B2 in univ[i:l] }

interactive bunionType {| intro [] |} :
   [wf] sequent { <H> >- "type"{'A} } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- "type"{'A bunion 'B} }

doc <:doc<
   (* Formation. *)
   @docoff
>>
interactive bunionFormation :
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] } -->
   sequent { <H> >- univ[i:l] }

doc <:doc<
   @modsubsection{Membership}

   Two terms are equal in the binary union if they are equal
   in either type.
>>
interactive bunionMemberEqualityLeft {| intro [SelectOption 1] |} :
   [wf] sequent { <H> >- 'x = 'y in 'A } -->
   [wf] sequent { <H> >- "type"{'B} } -->
   sequent { <H> >- 'x = 'y in 'A bunion 'B }

interactive bunionMemberEqualityRight {| intro [SelectOption 2] |} :
   [wf] sequent { <H> >- 'x = 'y in 'B } -->
   [wf] sequent { <H> >- "type"{'A} } -->
   sequent { <H> >- 'x = 'y in 'A bunion 'B }

doc <:doc<
   @modsubsection{Elimination}

   The elimination form retains the limitations of the
   general union elimination @hrefrule[tunionElimination]: it
   can be used only for equality judgments.  The elimination form
   for a union type $@bunion{A; B}$ produces two cases: one for
   membership in $A$, and another for membership in $B$.
>>
interactive bunionElimination 'H :
   [main] sequent { <H>; 'A bunion 'B; x: 'A; <J['x]> >- squash{'C['x]} } -->
   [main] sequent { <H>; 'A bunion 'B; x: 'B; <J['x]> >- squash{'C['x]} } -->
   sequent { <H>; x: 'A bunion 'B; <J['x]> >- squash{'C['x]} }

doc docoff

let bunionElimT = argfunT (fun i p ->
   (if is_squash_term (concl p) then
      bunionElimination i
   else 
      (squashT thenT bunionElimination i thenT unsquashT 0))
   thenT thinIfThinningT [i]) 

let resource elim += << 'A bunion 'B >>, wrap_elim bunionElimT

(*
 * -*-
 * Local Variables:
 * End:
 * -*-
 *)
