doc <:doc<
   @begin[doc]
   @module[Itt_field]

   This theory defines fields.
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
extends Itt_ring
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
open Itt_ring

let _ =
   show_loading "Loading Itt_field%t"

(************************************************************************
 * FIELD                                                                *
 ************************************************************************)

doc <:doc<
   @begin[doc]
   @modsection{Field}
   @modsubsection{Rewrites}

   @end[doc]
>>

define unfold_prefield1 : prefield[i:l] <-->
   record["inv":t]{r. 'r^car0 -> 'r^car0 ; record["car0":t]{univ[i:l];ring[i:l]}}

(*
 * This definition is not well-formed
 *
 * define unfold_isField1 : isField{'F} <-->
 *		'F^car0 subtype 'F^car &
 *		all a: 'F^car. (('a <> 'F^"0" in 'F^car) => ('a in 'F^car0)) &
 *		all b: 'F^car0. (('b in 'F^car) & ('b <> 'F^"0" in 'F^car)) &
 *		all c: 'F^car0. ('F^inv 'c) *['F] 'c = 'F^"1" in 'F^car
 *)

define unfold_isField1 : isField[i:l]{'F} <-->
	'F^car0 = {a: 'F^car | 'a <> 'F^"0" in 'F^car} in univ[i:l] &
	all c: 'F^car0. ('F^inv 'c) *['F] 'c = 'F^"1" in 'F^car

(* I'm going to try this definition next.
define unfold_isField1 : isField{'F} <-->
	ext_equal{ 'F^car0; {a: 'F^car | 'a <> 'F^"0" in 'F^car} } &
	all c: 'F^car0. ('F^inv 'c) *['F] 'c = 'F^"1" in 'F^car
*)

define unfold_field1 : field[i:l] <-->
   { F: prefield[i:l] | isField[i:l]{'F} }

define unfold_as_multiplicative_group : as_multiplicative_group{'F} <-->
	rename["car":t,"car0":t]{'F}

doc docoff

let unfold_prefield = unfold_prefield1
let unfold_isField = unfold_isField1
let unfold_field = unfold_field1 thenC addrC [0] unfold_prefield thenC addrC [1] unfold_isField

let fold_prefield1 = makeFoldC << prefield[i:l] >> unfold_prefield1
let fold_prefield = makeFoldC << prefield[i:l] >> unfold_prefield
let fold_isField1 = makeFoldC << isField[i:l]{'F} >> unfold_isField1
let fold_isField = makeFoldC << isField[i:l]{'F} >> unfold_isField
let fold_field1 = makeFoldC << field[i:l] >> unfold_field1
let fold_field = makeFoldC << field[i:l] >> unfold_field
let fold_as_multiplicative_group = makeFoldC << as_multiplicative_group{'F} >> unfold_as_multiplicative_group

let fieldDT n = rw unfold_field n thenT dT n

let resource elim +=
   [<<field[i:l]>>, fieldDT]

doc <:doc<
   @begin[doc]
   @modsubsection{Well-formedness}

   @end[doc]
>>

interactive prefield_wf {| intro [] |} :
   sequent { <H> >- "type"{prefield[i:l]} }

interactive prefield_add_wf {| intro [intro_typeinf <<'F>>] |} prefield[i:l] :
   sequent { <H> >- 'F in prefield[i:l] } -->
   sequent { <H> >- 'a in 'F^car } -->
   sequent { <H> >- 'b in 'F^car } -->
   sequent { <H> >- 'a  +['F] 'b in 'F^car }

interactive prefield_mul_wf {| intro [intro_typeinf <<'F>>] |} prefield[i:l] :
   sequent { <H> >- 'F in prefield[i:l] } -->
   sequent { <H> >- 'a in 'F^car } -->
   sequent { <H> >- 'b in 'F^car } -->
   sequent { <H> >- 'a *['F] 'b in 'F^car }

interactive prefield_inv_wf {| intro [intro_typeinf <<'F>>] |} prefield[i:l] :
   sequent { <H> >- 'F in prefield[i:l] } -->
   sequent { <H> >- 'a in 'F^car } -->
   sequent { <H> >- 'a *['F] 'b in 'F^car }

interactive prefield_intro {| intro [] |} :
   sequent { <H> >- 'F in record["inv":t]{r. 'r^car0 -> 'r^car0 ; record["car0":t]{univ[i:l];ring[i:l]}} } -->
   sequent { <H> >- 'F in prefield[i:l] }

interactive prefield_elim {| elim [] |} 'H :
   sequent { <H>; F: record["inv":t]{r. 'r^car0 -> 'r^car0 ; record["car0":t]{univ[i:l];ring[i:l]}}; <J['F]> >- 'C['F] } -->
   sequent { <H>; F: prefield[i:l]; <J['F]> >- 'C['F] }

interactive isField_wf {| intro [intro_typeinf <<'F>>] |} prefield[i:l] :
   sequent { <H> >- 'F in prefield[i:l] } -->
   sequent { <H> >- isField[i:l]{'F} Type }

interactive field_wf {| intro [] |} :
   sequent { <H> >- "type"{field[i:l]} }

interactive field_intro {| intro [] |} :
   [wf] sequent { <H> >- 'F in prefield[i:l] } -->
   [main] sequent { <H> >- isField[i:l]{'F} } -->
   sequent { <H> >- 'F in field[i:l] }

interactive field_elim {| elim [] |} 'H :
   sequent { <H>; F: prefield[i:l]; v: isField[i:l]{'F}; <J['F]> >- 'C['F] } -->
   sequent { <H>; F: field[i:l]; <J['F]> >- 'C['F] }

doc <:doc<
   @begin[doc]
   @modsubsection{Hierarchy}

   A field is a ring and group wrt to multiplicative operations over car0.
   @end[doc]
>>
interactive field_subtype_ring :
   sequent { <H> >- field[i:l] subtype ring[i:l] }

interactive field_subtype_group :
   sequent { <H> >- 'F in field[i:l] } -->
   sequent { <H> >- as_multiplicative_group{'F} in group[i:l] }

doc docoff

dform field_df1 : except_mode[src] :: except_mode[prl] :: field[i:l] =
   mathbbF `"ield" sub{slot[i:l]}

dform ring_df2 : mode[prl] :: field[i:l] =
   `"field[" slot[i:l] `"]"

dform prering_df1 : except_mode[src] :: except_mode[prl] :: prefield[i:l] =
   `"prefield" sub{slot[i:l]}

dform prering_df2 : mode[prl] :: prefield[i:l] =
   `"prefield[" slot[i:l] `"]"

(*
 * -*-
 * Local Variables:
 * Caml-master: "prlcomp.run"
 * End:
 * -*-
 *)
