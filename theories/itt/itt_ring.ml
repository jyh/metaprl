doc <:doc<
   @begin[doc]
   @module[Itt_ring]

   This theory defines rings.
   @end[doc]

   ----------------------------------------------------------------

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

   Author: Yegor Bryukhov @email{ybryukhov@gc.cuny.edu}
   @end[license]
>>

doc <:doc< @doc{@parents} >>
extends Itt_group
extends Itt_bisect
(*extends Itt_subset
extends Itt_subset2
extends Itt_ext_equal*)
extends Itt_record_renaming
extends Itt_grouplikeobj
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
   show_loading "Loading Itt_ring%t"

declare agroup[i:l]
declare aabelg[i:l]

prim agroupEquality {| intro [] |} :
   sequent { <H> >- 'G1='G2 in group[i:l] } -->
   sequent { <H> >- rename_mul_add{'G1}=rename_mul_add{'G2} in agroup[i:l] } = it

prim additiveEqualityInGroup {| intro [] |} :
   sequent { <H> >- 'G1='G2 in agroup[i:l] } -->
   sequent { <H> >- as_additive{'G1}=as_additive{'G2} in group[i:l] } = it

interactive agroup_wf {| intro [] |} :
   sequent { <H> >- "type"{agroup[i:l]} }

interactive agroupWeakElimination 'H bind{x.'C['x]} :
	sequent { <H>; <J>; g: group[i:l] >- 'C['g] } -->
	sequent { <H>; g: agroup[i:l]; <J> >- 'C[as_additive{'g}] }

interactive agroupElimination {| elim [] |} 'H :
	sequent { <H>; <J>; g: group[i:l] >- 'C[rename_mul_add{'g}] } -->
	sequent { <H>; g: agroup[i:l]; <J> >- 'C['g] }

interactive agroupEquality2 {| intro [] |} :
   sequent { <H> >- as_additive{'G1}=as_additive{'G2} in group[i:l] } -->
   sequent { <H> >- 'G1='G2 in agroup[i:l] }

(*
 * <J[as_additive{'g}]> is not supported because it has to be specified as a rule parameter
 *
 * interactive agroupFullWeakElimination {| elim [] |} sequent{<H>; g: agroup[i:l]; <J['g]> >- 'C['g] } :
 *	sequent { <H>; g: group[i:l]; <J['g]> >- 'C['g] } -->
 *	sequent { <H>; g: agroup[i:l]; <J[as_additive{'g}]> >- 'C[as_additive{'g}] }
 *
 *
 * This version of elimination rule is probably stronger than introduction rules but we possibly don't need it
 *
 * prim agroupElimination {| elim [] |} 'H :
 *	sequent { <H>; g: group[i:l]; <J[rename_mul_add{'g}]> >- 'C[rename_mul_add{'g}] } -->
 *	sequent { <H>; g: agroup[i:l]; <J['g]> >- 'C['g] }
 *)

interactive agroup_add_wf {| intro [intro_typeinf <<'R>>] |} agroup[i:l] :
   sequent { <H> >- 'R in agroup[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a +['R] 'b in 'R^car }

prim aabelgEquality {| intro [] |} :
   sequent { <H> >- 'G1='G2 in abelg[i:l] } -->
   sequent { <H> >- rename_mul_add{'G1}=rename_mul_add{'G2} in aabelg[i:l] } = it

prim additiveEqualityInAbelG {| intro [] |} :
   sequent { <H> >- 'G1='G2 in aabelg[i:l] } -->
   sequent { <H> >- as_additive{'G1}=as_additive{'G2} in abelg[i:l] } = it

interactive aabelg_wf {| intro [] |} :
   sequent { <H> >- "type"{aabelg[i:l]} }

interactive aabelgWeakElimination 'H bind{x.'C['x]} :
	sequent { <H>; <J>; g: abelg[i:l] >- 'C['g] } -->
	sequent { <H>; g: aabelg[i:l]; <J> >- 'C[as_additive{'g}] }

interactive aabelgElimination {| elim [] |} 'H :
	sequent { <H>; <J>; g: abelg[i:l] >- 'C[rename_mul_add{'g}] } -->
	sequent { <H>; g: aabelg[i:l]; <J> >- 'C['g] }

interactive aabelgEquality2 {| intro [] |} :
   sequent { <H> >- as_additive{'G1}=as_additive{'G2} in abelg[i:l] } -->
   sequent { <H> >- 'G1='G2 in aabelg[i:l] }

(************************************************************************
 * RING                                                                 *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Ring}
   @modsubsection{Rewrites}

   @end[doc]
>>
define unfold_prering1 : prering[i:l] <-->
   bisect{monoid[i:l]; aabelg[i:l]}

define unfold_isDistrib1 : isDistrib{'R} <-->
	all a: 'R^car. all b: 'R^car. all c: 'R^car. 'a *['R] ('b +['R] 'c) = ('a *['R] 'b) +['R] ('a *['R] 'c) in 'R^car

define unfold_ring1 : ring[i:l] <-->
   {R: prering[i:l] | isDistrib{'R}}
doc docoff

let unfold_prering = unfold_prering1 (*thenC addrC [0] unfold_monoid*)
let unfold_isDistrib = unfold_isDistrib1
let unfold_ring = unfold_ring1 thenC addrC [0] unfold_prering thenC addrC [1] unfold_isDistrib

let fold_prering1 = makeFoldC << prering[i:l] >> unfold_prering1
let fold_prering = makeFoldC << prering[i:l] >> unfold_prering
let fold_isDistrib1 = makeFoldC << isDistrib{'R} >> unfold_isDistrib1
let fold_isDistrib = makeFoldC << isDistrib{'R} >> unfold_isDistrib
let fold_ring1 = makeFoldC << ring[i:l] >> unfold_ring1
let fold_ring = makeFoldC << ring[i:l] >> unfold_ring

let ringDT n = rw unfold_ring n thenT dT n

let resource elim +=
   [<<ring[i:l]>>, ringDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>

interactive prering_wf {| intro [] |} :
   sequent { <H> >- "type"{prering[i:l]} }

interactive prering_car_wf {| intro [intro_typeinf <<'R>>] |} prering[i:l] :
   sequent { <H> >- 'R in prering[i:l] } -->
   sequent { <H> >- 'R^car Type }

interactive prering_add_wf {| intro [intro_typeinf <<'R>>] |} prering[i:l] :
   sequent { <H> >- 'R in prering[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a  +['R] 'b in 'R^car }

interactive prering_mul_wf {| intro [intro_typeinf <<'R>>] |} prering[i:l] :
   sequent { <H> >- 'R in prering[i:l] } -->
   sequent { <H> >- 'a in 'R^car } -->
   sequent { <H> >- 'b in 'R^car } -->
   sequent { <H> >- 'a *['R] 'b in 'R^car }

interactive isDistrib_wf {| intro [intro_typeinf <<'R>>] |} prering[i:l] :
   sequent { <H> >- 'R in prering[i:l] } -->
   sequent { <H> >- isDistrib{'R} Type }

interactive ring_wf {| intro [] |} :
   sequent { <H> >- "type"{ring[i:l]} }

doc <:doc<
   @begin[doc]
   @modsubsection{Introduction and Elimination}

   @end[doc]
>>
interactive prering_intro {| intro [] |} :
   sequent { <H> >- 'R in monoid[i:l] } -->
   sequent { <H> >- 'R in aabelg[i:l] } -->
   sequent { <H> >- 'R in prering[i:l] }

interactive prering_elim {| elim [] |} 'H :
   sequent { <H>; R: bisect{monoid[i:l]; aabelg[i:l]}; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: prering[i:l]; <J['R]> >- 'C['R] }

interactive ring_intro {| intro [] |} :
   [wf] sequent { <H> >- 'R in prering[i:l] } -->
   [main] sequent { <H> >- isDistrib{'R} } -->
   sequent { <H> >- 'R in ring[i:l] }

interactive ring_elim {| elim [] |} 'H :
   sequent { <H>; R: prering[i:l]; v: isDistrib{'R}; <J['R]> >- 'C['R] } -->
   sequent { <H>; R: ring[i:l]; <J['R]> >- 'C['R] }

doc <:doc<
   @begin[doc]
   @modsubsection{Hierarchy}

   A ring is also a monoid wrt multiplicative operations and
   group wrt additive operations.
   @end[doc]
>>
interactive ring_subtype_monoid :
   sequent { <H> >- ring[i:l] subtype monoid[i:l] }

interactive ring_subtype_aabelg :
   sequent { <H> >- ring[i:l] subtype aabelg[i:l] }
doc docoff

define unfoldZ : Z <-->
	{car=int; "*"=lambda{x.lambda{y.('x *@ 'y)}}; "1"=1;
	 "+"=lambda{x.lambda{y.('x +@ 'y)}}; "0"=0; "neg"=lambda{x.(- 'x)}}

let foldZ = makeFoldC << Z >> unfoldZ

interactive int_ring_is_ring :
	sequent { <H> >- Z in ring[i:l] }

dform ring_df1 : except_mode[src] :: except_mode[prl] :: ring[i:l] =
   mathbbR `"ing" sub{slot[i:l]}

dform ring_df2 : mode[prl] :: ring[i:l] =
   `"ring[" slot[i:l] `"]"

dform prering_df1 : except_mode[src] :: except_mode[prl] :: prering[i:l] =
   `"prering" sub{slot[i:l]}

dform prering_df2 : mode[prl] :: prering[i:l] =
   `"prering[" slot[i:l] `"]"

dform int_ring_df1 : except_mode[src] :: Z =
   mathbbZ

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
