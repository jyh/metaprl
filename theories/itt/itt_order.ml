doc <:doc<
   @begin[doc]
   @module[Itt_order]

   This theory defines ordered sets.
   @end[doc]

   ----------------------------------------------------------------

   @begin[license]
   This file is part of MetaPRL, a modular, higher order
   logical framework that provides a logical programming
   environment for OCaml and other languages.

   See the file doc/index.html for information on Nuprl,
   OCaml, and more information about this system.

   Copyright (C) 2003 Yegor Bryukhov, GC CUNY

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

   Author: Yegor Bryukhov @email{ybryukhov@gc.cuny.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_bisect
(*extends Itt_subset
extends Itt_subset2
extends Itt_ext_equal*)
extends Itt_record
extends Itt_record_renaming
doc docoff

open Lm_debug
open Refiner.Refiner.TermOp

open Tactic_type.Tacticals

open Dtactic
open Top_conversionals

open Itt_struct
open Itt_bisect
open Itt_grouplikeobj
open Itt_group
open Itt_squash
open Itt_equal
open Itt_subtype
open Itt_record_renaming

let _ =
   show_loading "Loading Itt_order%t"

(************************************************************************
 * RELATION, PARTIAL ORDER                                              *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Partial order}
   @modsubsection{Rewrites}

   @end[doc]
>>

define unfold_relation : relation[i:l, rel:t] <-->
	record[rel:t]{r. 'r^car -> 'r^car -> univ[i:l]; {car: univ[i:l]} }

define unfold_isReflexive : isReflexive[rel:t]{'O} <-->
	all a: 'O^car. field[rel:t]{'O} 'a 'a

define unfold_isAntisym : isAntisym[rel:t]{'O} <-->
	all a: 'O^car. all b: 'O^car. ((field[rel:t]{'O} 'a 'b) & (field[rel:t]{'O} 'b 'a) => ('a='b in 'O^car))

define unfold_isTransitive : isTransitive[rel:t]{'O} <-->
	all a: 'O^car. all b: 'O^car. all c: 'O^car. ((field[rel:t]{'O} 'a 'b) & (field[rel:t]{'O} 'b 'c) => (field[rel:t]{'O} 'a 'c))

define unfold_isPartialOrder1 : isPartialOrder[rel:t]{'O} <-->
	isReflexive[rel:t]{'O} & isTransitive[rel:t]{'O} & isAntisym[rel:t]{'O}

define unfold_partialOrder1 : partialOrder[i:l,rel:t] <-->
   { O: relation[i:l,rel:t] | isPartialOrder[rel:t]{'O} }

doc docoff

let unfold_isPartialOrder = unfold_isPartialOrder1 thenC addrC [0] unfold_isReflexive thenC addrC [1;0] unfold_isTransitive thenC addrC [1;1] unfold_isAntisym
let unfold_partialOrder = unfold_partialOrder1 thenC addrC [0] unfold_relation thenC addrC [1] unfold_isPartialOrder

let fold_relation = makeFoldC << relation[i:l,rel:t] >> unfold_relation
let fold_isReflexive = makeFoldC << isReflexive[rel:t]{'O} >> unfold_isReflexive
let fold_isTransitive = makeFoldC << isTransitive[rel:t]{'O} >> unfold_isTransitive
let fold_isAntisym = makeFoldC << isAntisym[rel:t]{'O} >> unfold_isAntisym
let fold_isPartialOrder1 = makeFoldC << isPartialOrder[rel:t]{'O} >> unfold_isPartialOrder
let fold_isPartialOrder = makeFoldC << isPartialOrder[rel:t]{'O} >> unfold_isPartialOrder
let fold_partialOrder1 = makeFoldC << partialOrder[i:l,rel:t] >> unfold_partialOrder1
let fold_partialOrder = makeFoldC << partialOrder[i:l,rel:t] >> unfold_partialOrder

let partialOrderDT n = rw unfold_partialOrder1 n thenT dT n

let resource elim +=
   [<<partialOrder[i:l,rel:t]>>, partialOrderDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>

interactive relation_wf {| intro [] |} :
   sequent { <H> >- relation[i:l,rel:t] Type }

interactive relation_intro {| intro [] |} :
   sequent { <H> >- 'R in record[rel:t]{r. 'r^car -> 'r^car -> univ[i:l]; {car: univ[i:l]} } } -->
   sequent { <H> >- 'R in relation[i:l,rel:t] }

interactive relation_elim {| elim [] |} 'H :
   sequent { <H>; R: record[rel:t]{r. 'r^car -> 'r^car -> univ[i:l]; {car: univ[i:l]} }; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: relation[i:l,rel:t]; <J['R]> >- 'C['R] }

interactive isPartialOrder_wf {| intro [intro_typeinf <<'R>>] |} relation[i:l,rel:t] :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isPartialOrder[rel:t]{'R} Type }

interactive partialOrder_wf {| intro [] |} :
	sequent { <H> >- partialOrder[i:l,rel:t] Type }

interactive partialOrder_intro {| intro [] |} :
   sequent { <H> >- 'R in relation[i:l,rel:t] } -->
	sequent { <H> >- isPartialOrder[rel:t]{'R} } -->
   sequent { <H> >- 'R in partialOrder[i:l,rel:t] }
